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
import Acorn.Host.Certificate
import Acorn.Host.Checkpoint.Snapshot
import Acorn.Host.Cli
import Acorn.Host.Viewer.ControlRequest
import Acorn.Host.Viewer.GoalProtocol
import Acorn.Host.Viewer.WireNumber
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

## Selection rule

A decision is registered here when a theorem beside its definition proves a property of its
accepted or refused results, or when the inputs it accepts follow by unfolding its definition
in this module. The property is the set of accepted or refused inputs where a theorem states
one, and otherwise what an accepted or a refused result is; each contract's docstring says
which. Four groups are registered.

* Decisions of independent arguments carry a kind and the registration. A function of several
  arguments is decided on their product through `Function.uncurry`.
* A decision procedure whose result type is `Decidable _` carries both directions in its type,
  so it is registered with no contract.
* An admission with an argument or result type that depends on an earlier argument, such as
  `Bounded32.admit`, has no kind: a kind is stated about a function between two fixed types.
  The proved statement is registered as an ordinary requirement, which the audit reports with
  no kind, and the function carries no `@[regula_decision]` registration. The ownership audit
  requires each such contract by name instead, with a statement that still refers to the
  executing definition.
* A function between fixed types for which no proof supplies the witness of a kind has no kind
  either. Each kind carries an input the function accepts or one it refuses. For
  `Host.impassable` and `Host.walkableTile` that input is the generated terrain of one tile,
  and no theorem states the terrain of a tile. The proved statement is registered as an
  ordinary requirement, and the ownership audit requires it in the same way.

A contract whose proof needs the proof library is stated in `AcornVerif.Decisions`. Regula
counts only a contract of the function's own library toward a registration, so such a function
is not registered here, and the ownership audit requires its contract in the same way. The
certificate checkers `Host.replayCertified`, `Host.regionBlocked` and `Host.stanceCertified`
are stated there, with `Host.walkableTile`: what an accepted certificate establishes is a
statement about runs of the executed world step, proved in `AcornVerif.CurrentCertificates`.
No checker is complete, so `Host.regionBlocked` carries the sound kind and the other two, whose
arguments have a dependent type, an ordinary requirement.

## Decisions that are not registered

The Regula audit requires a contract of a registered function whose result type is not
`Decidable _`, and it does not find a decision that is not registered. The groups below are
not registered; each is recorded with the evidence that stands for it.

This record covers the `Acorn` library. `NativeApp` and `Bootstrap` are separate claimed
libraries: Regula counts only a contract of the function's own library and refuses a
registration written for a declaration of another, so this module can register none of their
functions. The parsers of `NativeApp` are `NativeApp.decodeBuildIdentity`,
`NativeApp.auditHex` and `NativeApp.auditOptions`, each of fixed types with no theorem about
the inputs it accepts. `Bootstrap` decides only in `IO`. The proof library `AcornVerif` has no
executable, so no claim rests on running one of its definitions. Its definitions with an
optional or Boolean result, such as `AcornVerif.Checkpoint.authorize`,
`AcornVerif.CurrentStep.passable` and `AcornVerif.CurrentGridWorld.advance`, are models that
its theorems relate to the executing definitions. Its interaction kernel and world classes
(`AcornVerif.Kernel`, `AcornVerif.WorldClass`) state worlds, agents, goals and bounds as
structures and propositions.

* An admission that applies other admissions in sequence has no contract of its own.
  `Prediction.admit` and `LogStepSize.admit` are `Bounded32.admit` at a derived interval,
  `Lifetime.SumCount.admit` is the body of `Checkpoint.admitSum`, and `Assignment.admitUsing`
  is the body of `Assignment.admit`, which applies it at the bank's slot function
  (`Assignment.wordsUsing_roundtrip`). `Controller.stepRaw` and
  `PredictionControl.advanceRaw` refuse exactly when `Action.admit` does
  (`Controller.stepRaw_refuses`, `PredictionControl.raw_refusal`), `Agent.restore` exactly
  when the resumable-profile test does (`Agent.restore_refuses`), and `FeatureProfile.admit`
  applies that test before `FeatureImage.admit` (`FeatureProfile.unsupported_refuses`).
  `FeatureImage.admit`, `Checkpoint.admitDemons`, `Checkpoint.admitPayload` and
  `Checkpoint.loadCandidate` compose the checkpoint admissions; their round trips are proved
  in `AcornVerif.CurrentCheckpoint` (`feature_roundtrip`, `demons_roundtrip`,
  `image_roundtrip`, `candidate_roundtrip`). `Host.Position.translate` applies
  `Host.Coordinate.checked` to each coordinate. `Host.Viewer.coreTelemetryLine` and
  `Host.Viewer.controlTelemetryLine` apply `wireText` to the line they emit, and
  `Host.Viewer.WorldMemory.frame` applies `sseLine` to its frame. An accepting result of
  `Host.Viewer.authorizeCommand` carries the verdicts of `ControlHeaders.authorizes` and
  `controlCommand` as fields of its type. `Host.CertificateDriver.execute` refuses when
  `Host.WorldConfig.standard` or world generation does, or when the standard curriculum does
  not hold a reach goal at each of the two indices it reads.
* A function that proposes a certificate decides nothing. `Host.CertificateSearch.explore`,
  `pathTo`, `settle` and `region`, with their helpers `neighbor`, `behind`, `kindAt`,
  `arrivalDirection`, `inGoalBox` and `Findings.complete`, propose candidates, and nothing is
  proved about them: a proposal means nothing until its checker accepts it.
  `Host.CertificateDriver.certifyReach` and `certifyItem` pass each proposal to its checker
  and keep the certificate the checker returns.
* `Host.Viewer.Buffer.offer`, `Checkpoint.decodeList` and `Checkpoint.decodeListInto` are
  polymorphic in their element type, which no kind admits. `Buffer.offer_iff` states the
  acceptance of the first, and `Checkpoint.list_roundtrip` and
  `Checkpoint.list_into_roundtrip` the round trips of the other two. Every
  `Checkpoint.Codec` carries the round trip of its own decoder as a field.
* An effect with a pure core is covered through that core. `Checkpoint.loadFile` returns the
  verdict of `Checkpoint.load` on the bytes it read, and `Checkpoint.Store.save` refuses with
  `Checkpoint.saveBytes`; both cores are registered below. `Host.CertificateDriver.dispatch`
  admits its arguments with `Host.CertificateDriver.natural` and `Host.Coordinate.checked` and
  prints what `execute` returns. An effect with no pure core decides from state outside the
  Lean definitions, so no theorem states its verdict:
  `Host.StopFlag.requested` and the `Host.Viewer.Broadcast` operations read shared state under
  a lock, `Host.Viewer.RunDirectory.adoptStrayCheckpoint` reads the file system and
  `Host.Viewer.NativeResources.observe` reads the operating system. The concurrency and
  operating-system assumptions of the verification guide stand for them.
* A parser or test of fixed types with no theorem about the inputs it accepts is not
  registered, because no direction of its verdict is proved. Nothing states which inputs it
  accepts; what stands is the type of an accepted value alone. These are the command-line
  parsers `Host.Cli.scan`, `Host.Cli.value`, `Host.Cli.required`, `Host.Cli.natural`,
  `Host.Cli.unsigned`, `Host.Cli.side`, `Host.Cli.profile`, `Host.Cli.criterion`,
  `Host.Cli.command`, `Host.Cli.demo`, `Host.Cli.dispatch`, `Host.AgentArguments.profile`,
  `Host.AgentArguments.word`, `Host.AgentArguments.admit`, `Host.Viewer.ViewerOptions.decode`,
  `Host.CertificateDriver.natural` and `Host.parseControl`; the JSON parser `Json.parse` with
  its readers `Json.Value.text`, `Json.Value.natural`, `Json.Value.list`, `Json.Value.fields`
  and `Json.decode`; and the
  viewer parsers `Host.Viewer.Command.parse`, `Host.Viewer.controlCommand`,
  `Host.Viewer.jsonField`, `Host.Viewer.jsonWord`, `Host.Viewer.jsonBrowserClock`,
  `Host.Viewer.jsonBool`, `Host.Viewer.runWord`, `Host.Viewer.healthFromJson`,
  `Host.Viewer.captureFromJson`, `Host.Viewer.HealthEnvelope.parse`,
  `Host.Viewer.Envelope.parse`, `Host.Viewer.LineBytes.text`, `Host.Viewer.terrainFromJson`,
  `Host.Viewer.sensedFromJson`, `Host.Viewer.SensedEnvelope.parse`,
  `Host.Viewer.coreIdentityFromJson`, `Host.Viewer.coreIdentity`,
  `Host.Viewer.PersistedState.decode`, `Host.Viewer.residentBytes`,
  `Host.Viewer.MapBytes.admit`, `Host.Viewer.decodeMapRuns`, `Host.Viewer.decodeMap` and
  `Host.Viewer.mapRunsBase64`. Kinds for these parsers against written grammars are the
  subject of https://github.com/rbeauchamp/acorn/issues/81. The path test
  `Checkpoint.temporaryPath` and the identity test `Host.Viewer.Identity.browserSafe` are in
  this group too.
* A Boolean predicate over state the library has already admitted, such as
  `Host.Viewer.Lifecycle.acceptsFailure`, `Host.Viewer.Capture.follows` or
  `Features.Lifecycle.eligible`, selects a branch of a transition and has no contract. The
  theorems about those transitions stand; for the viewer the ownership audit requires
  `Lifecycle.stale_preserves`, `Lifecycle.retire_revokes` and
  `Admission.rejected_preserves_history`.
* A derived `DecidableEq` or `BEq` instance is generated by Lean and is not registered.

A definition whose optional or Boolean result reports a selection, a lookup or the outcome of
a state transition is not a decision in this sense.

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

/-- A prediction word of the Demon-0 range is a bonus exactly when its signed key is
positive. -/
theorem bonus_of_weight : Regula.ExecutableContract Bonus.ofWeight
    (Regula.Decides (·.isSome = true)
      (fun weight : Prediction .g99 => 0 < weight.value.key)) :=
  ⟨decides
    (fun weight => by
      show (Bonus.ofWeight weight).isSome = true ↔ _
      unfold Bonus.ofWeight
      split <;> simp_all)
    ⟨⟨⟨0x3f800000⟩, by decide⟩, by decide⟩ ⟨⟨.zero, by decide⟩, by decide⟩⟩

attribute [regula_decision] Bonus.ofWeight

/-- Prediction-list admission accepts exactly the lists within the prediction-channel count. -/
theorem predictions_admit : Regula.ExecutableContract Predictions.admit
    (Regula.Decides (·.isSome = true)
      (fun values : List Binary32 => values.length ≤ Acorn.FeatureConstants.demonCount)) :=
  ⟨decides (fun _ => dite_isSome _) ⟨[], Nat.zero_le _⟩
    ⟨List.replicate (Acorn.FeatureConstants.demonCount + 1) .zero, by simp⟩⟩

attribute [regula_decision] Predictions.admit

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

/-! ## Certificate tests

The checkers of `Host.Certificate` decide a certificate by these tests of one tile. The checkers
themselves are registered in `AcornVerif.Decisions`, with what an accepted certificate
establishes, and below with the admissions of a dependent type. -/

/-- The region test accepts exactly a tile that is one of the listed cells
(`AcornVerif.CurrentCertificates.inRegion_iff`). -/
theorem region_member : Regula.ExecutableContract Host.inRegion (fun test =>
    Regula.Decides (· = true)
      (fun input : List Host.Position × Host.Position => input.2 ∈ input.1)
      (Function.uncurry test)) :=
  ⟨decides (fun input => by simp [Function.uncurry, Host.inRegion])
    ⟨([⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩], ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩),
      List.mem_singleton.mpr rfl⟩
    ⟨([], ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩), List.not_mem_nil⟩⟩

attribute [regula_decision] Host.inRegion

/-- The box test accepts exactly the tiles with both coordinates inside the side of the
receiving box. `AcornVerif.CurrentCertificates.inBox_position` states that it accepts every
body position. -/
theorem box_member : Regula.ExecutableContract Host.inBox (fun test =>
    Regula.Decides (· = true)
      (fun input : Host.WorldConfig × Host.Position =>
        (0 ≤ input.2.x.val ∧ input.2.x.val < input.1.side) ∧
          (0 ≤ input.2.y.val ∧ input.2.y.val < input.1.side))
      (Function.uncurry test)) :=
  ⟨decides
    (fun input => by
      show (Host.BoxPosition.checked input.1 input.2.x.val input.2.y.val).isSome = true ↔ _
      unfold Host.BoxPosition.checked
      by_cases column : 0 ≤ input.2.x.val ∧ input.2.x.val < input.1.side
      · by_cases row : 0 ≤ input.2.y.val ∧ input.2.y.val < input.1.side <;>
          simp [column, row]
      · simp [column])
    ⟨(⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide, by decide⟩,
        ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩), by decide⟩
    ⟨(⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide, by decide⟩,
        ⟨⟨-1, by decide⟩, ⟨0, by decide⟩⟩), by decide⟩⟩

attribute [regula_decision] Host.inBox

/-- The cover test accepts exactly an absent tile, a listed tile and a tile outside the
receiving box. -/
theorem region_covers : Regula.ExecutableContract Host.covered (fun test =>
    Regula.Decides (· = true)
      (fun input : (Host.WorldConfig × List Host.Position) × Option Host.Position =>
        ∀ tile, input.2 = some tile → tile ∈ input.1.2 ∨ Host.inBox input.1.1 tile = false)
      (Function.uncurry (Function.uncurry test))) :=
  ⟨decides
    (fun ⟨⟨config, cells⟩, candidate⟩ => by
      cases candidate with
      | none => simp [Function.uncurry, Host.covered]
      | some tile => simp [Function.uncurry, Host.covered, Host.inRegion])
    ⟨((⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide, by decide⟩, []), none),
      fun _ absent => nomatch absent⟩
    ⟨((⟨⟨0, ⟨1, by decide⟩, 1, 0, 0, 0, 0, .zero⟩, by decide, by decide⟩, []),
        some ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩),
      fun covers =>
        (covers _ rfl).elim List.not_mem_nil (fun outside => absurd outside (by decide))⟩⟩

attribute [regula_decision] Host.covered

/-- The impassable test accepts exactly a tile whose static terrain is a mountain, or water
when the certificate is for a body without a boat. It refuses a terrain refusal.

The function is between fixed types, but each kind carries an accepted or a refused input of
the function, which is the generated terrain of one tile, and no theorem states the terrain of
a tile. The statement is therefore an ordinary requirement with no kind. -/
theorem tile_impassable : Regula.ExecutableContract Host.impassable (fun test =>
    ∀ (config : Host.WorldConfig) (boat : Bool) (tile : Host.Position),
      test config boat tile = true ↔
        Host.terrain tile config.raw.seed config.raw.baseScale = .ok .mountain ∨
          (Host.terrain tile config.raw.seed config.raw.baseScale = .ok .water ∧
            boat = false)) :=
  ⟨fun config boat tile => by
    unfold Host.impassable
    cases Host.terrain tile config.raw.seed config.raw.baseScale with
    | error refusal => simp
    | ok kind => cases kind <;> simp⟩

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

/-- Binary32 field extraction accepts exactly the finite words. -/
theorem binary32_dyadic : Regula.ExecutableContract binary32Dyadic
    (Regula.Decides (·.isSome = true) (fun value : Binary32 => value.Finite)) :=
  ⟨decides
    (fun value => by
      show (binary32Dyadic value).isSome = true ↔ _
      unfold binary32Dyadic
      split <;> simp_all)
    ⟨.zero, by decide⟩ ⟨⟨0x7fc00000⟩, by decide⟩⟩

attribute [regula_decision] binary32Dyadic

/-- Binary64 field extraction accepts exactly the finite words. -/
theorem binary64_dyadic : Regula.ExecutableContract binary64Dyadic
    (Regula.Decides (·.isSome = true) (fun value : Binary64 => value.Finite)) :=
  ⟨decides
    (fun value => by
      show (binary64Dyadic value).isSome = true ↔ _
      unfold binary64Dyadic
      split <;> simp_all)
    ⟨⟨0⟩, by decide⟩ ⟨⟨0x7ff8000000000000⟩, by decide⟩⟩

attribute [regula_decision] binary64Dyadic

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
proposition and a refusing result a proof of its negation, so no contract is registered. The
instances are registered under the names Lean generates for them. -/

attribute [regula_decision] Interval32.orderedDecidable Binary32.positiveDecidable
  Binary32.instDecidableFinite Binary64.instDecidableFinite Interval32.instDecidableContains
  Features.instDecidableRecent Features.instDecidableDominates Lifetime.instDecidableLegalSum
  Checkpoint.instDecidableValid Checkpoint.instDecidableOptionsValid

/-! ## Admissions with a dependent type

An argument or result type of each function below is indexed by an earlier argument: the
receiving interval, the value rule, the feature dimension, the bank configuration or the agent
construction. A decision kind is stated about a function between two fixed types, so none
applies. The proved statement about each function is registered as an ordinary requirement,
reported with no kind. Its docstring says what the statement covers: the inputs the function
accepts or refuses, or a property of an accepted or a refused result. -/

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

/-- Rail admission accepts every configuration (`rails_admission_total`). -/
theorem rails_admit : Regula.ExecutableContract StepSizeRails.admit (fun admit =>
    ∀ config : Acorn.Config, admit config ≠ none) :=
  ⟨rails_admission_total⟩

/-- An admitted squared discrepancy is the exact squared discrepancy of the two words
(`Agreement.admitSquared_exact`).

**Not claimed:** which pairs of words the receiving envelope admits. -/
theorem squared_admit : Regula.ExecutableContract Agreement.admitSquared (fun admit =>
    ∀ (envelope : Nat) (forecast outcome : Binary32) (sample : Fin (envelope ^ 2 + 1)),
      admit envelope forecast outcome = some sample →
        sample.val = Agreement.squaredUnits forecast outcome) :=
  ⟨Agreement.admitSquared_exact⟩

/-- Event admission accepts the words of every bank-relative event and returns that event
(`Event.words_roundtrip`).

**Not claimed:** that every accepted word pair is the word image of an event. -/
theorem event_admit : Regula.ExecutableContract Event.admit (fun admit =>
    ∀ (config : Features.Config) (event : Event config),
      admit config event.words = some event) :=
  ⟨fun _ => Event.words_roundtrip⟩

/-- Latest-event admission accepts the words of every latest event, present or absent, and
returns it (`admitLast_roundtrip`).

**Not claimed:** that every accepted word triple is such an image. -/
theorem last_admit : Regula.ExecutableContract admitLast (fun admit =>
    ∀ (config : Features.Config) (last : Option (Event config)),
      admit config (lastWords last) = some last) :=
  ⟨fun _ => admitLast_roundtrip⟩

/-- Tester admission accepts the words of every legal tester state under its own clock and
returns that state (`Progress.words_roundtrip`).

**Not claimed:** that every accepted image is the word image of a legal state. -/
theorem progress_admit : Regula.ExecutableContract Progress.admit (fun admit =>
    ∀ (config : Features.Config) (progress : Progress config),
      admit config progress.clock progress.words = some progress) :=
  ⟨fun _ => Progress.words_roundtrip⟩

/-- Assignment admission accepts the words of every stored assignment of the receiving bank
and returns that assignment (`Assignment.words_roundtrip`).

**Not claimed:** that every accepted image is the word image of an assignment. -/
theorem assignment_admit : Regula.ExecutableContract Assignment.admit (fun admit =>
    ∀ (dimension : Dimension) (config : Features.Config) (assignment : Assignment config),
      admit dimension config (assignment.words dimension) = some assignment) :=
  ⟨fun dimension _ => Assignment.words_roundtrip dimension⟩

/-- Box admission accepts the coordinates of every position of the receiving box and returns
that position (`Host.BoxPosition.checked_position`).

**Not claimed:** that every accepted coordinate pair lies in the box. The result type states
that. -/
theorem box_position_checked : Regula.ExecutableContract Host.BoxPosition.checked
    (fun checked => ∀ (config : Host.WorldConfig) (position : Host.BoxPosition config),
      checked config position.position.x.val position.position.y.val = some position) :=
  ⟨fun _ => Host.BoxPosition.checked_position⟩

/-- Campaign admission accepts exactly a positive step cap with a repetition budget or a
nonempty goal range in the receiving curriculum. -/
theorem campaign_admit : Regula.ExecutableContract Host.CampaignPlan.admit (fun admit =>
    ∀ (size : Nat) (spec : Host.CampaignSpec), (admit size spec).isOk = true ↔
      0 < spec.steps.toNat ∧ (spec.cycles.toNat ≠ 0 ∨ 0 < min spec.goals.toNat size)) :=
  ⟨fun size spec => by
    unfold Host.CampaignPlan.admit
    by_cases steps : 0 < spec.steps.toNat
    · by_cases productive : spec.cycles.toNat ≠ 0 ∨ 0 < min spec.goals.toNat size
      · simp [steps, productive, Except.isOk, Except.toBool]
      · simp [steps, productive, Except.isOk, Except.toBool]
    · simp [steps, Except.isOk, Except.toBool]⟩

/-- The distinctness test accepts exactly the assignment tables in which no two slots hold the
same unit (`Assignment.distinct_iff`). -/
theorem assignment_distinct : Regula.ExecutableContract @Assignment.distinct (fun test =>
    ∀ (config : Features.Config)
      (table : Vector (Assignment config) Acorn.FeatureConstants.skillCount),
      @test config table = true ↔ Assignment.Distinct table) :=
  ⟨@Assignment.distinct_iff⟩

/-- Harvest-key admission accepts exactly the positions of the receiving box extended by one
tile on every side. -/
theorem harvest_key : Regula.ExecutableContract Host.harvestKey (fun admit =>
    ∀ (config : Host.WorldConfig) (position : Host.Position),
      (admit config position).isSome = true ↔
        (-1 ≤ position.x.val ∧ position.x.val ≤ config.side) ∧
          (-1 ≤ position.y.val ∧ position.y.val ≤ config.side)) :=
  ⟨fun config position => by
    unfold Host.harvestKey
    by_cases column : -1 ≤ position.x.val ∧ position.x.val ≤ config.side
    · by_cases row : -1 ≤ position.y.val ∧ position.y.val ≤ config.side <;>
        simp [column, row]
    · simp [column]⟩

/-- Map-index admission accepts exactly the coordinates inside the receiving map side. -/
theorem map_index : Regula.ExecutableContract mapIndex (fun admit =>
    ∀ (side : MapSide) (x y : Int), (admit side x y).isSome = true ↔
      0 ≤ x ∧ x < side.val ∧ 0 ≤ y ∧ y < side.val) :=
  ⟨fun side x y => by
    unfold mapIndex
    split <;> simp_all⟩

/-- Event-line admission accepts exactly the texts within the receiving capacity that hold
neither newline character. -/
theorem sse_line : Regula.ExecutableContract sseLine (fun admit =>
    ∀ (capacity : Nat) (text : String), (admit capacity text).isSome = true ↔
      text.utf8ByteSize ≤ capacity ∧ text.contains '\n' = false ∧
        text.contains '\r' = false) :=
  ⟨fun _ _ => dite_isSome _⟩

/-- Frame decoding accepts the encoding of every payload of the receiving dimension and
returns that payload (`Checkpoint.roundtrip`).

**Not claimed:** that every accepted byte list is the encoding of a payload. -/
theorem checkpoint_decode : Regula.ExecutableContract Checkpoint.decode (fun decode =>
    ∀ (dimension : Dimension) (payload : Checkpoint.Payload dimension),
      decode dimension (Checkpoint.encode dimension payload) = some payload) :=
  ⟨Checkpoint.roundtrip⟩

/-- The checkpoint writer refuses every state of a profile that is not resumable
(`Checkpoint.save_refuses`). `Checkpoint.save_supported` states that it writes every other
state. -/
theorem checkpoint_save : Regula.ExecutableContract Checkpoint.saveBytes (fun save =>
    ∀ (construction : AgentConstruction) (state : construction.State),
      construction.profile.checkpointSupported = false →
        save construction state = .error .unsupportedPolicy) :=
  ⟨Checkpoint.save_refuses⟩

/-- A refused checkpoint leaves its receiver unchanged: when loading refuses a byte list,
`Checkpoint.loadKeeping` returns the receiver it was given, with the refusal
(`Checkpoint.load_nonmutation`).

**Not claimed:** which byte lists are accepted. `AcornVerif.CurrentCheckpoint.save_load` states
that the bytes saved from a resumable profile load into a matching receiver. -/
theorem checkpoint_load : Regula.ExecutableContract Checkpoint.load (fun load =>
    ∀ (construction : AgentConstruction) (receiver : construction.State) (bytes : List UInt8)
      (error : Checkpoint.Error), load construction receiver bytes = .error error →
        Checkpoint.loadKeeping construction receiver bytes = (receiver, some error)) :=
  ⟨Checkpoint.load_nonmutation⟩

/-- Replay checking returns a certificate exactly when the replay checker accepts the action
list. The certificate's type carries that acceptance; `AcornVerif.Decisions.replay_certified`
states what it establishes. -/
theorem replay_check : Regula.ExecutableContract @Host.ReplayCertificate.check (fun check =>
    ∀ (config : Host.WorldConfig) (world : Host.World config) (goal : Host.Goal) (cap : Nat)
      (actions : List Host.Action),
      (@check config world goal cap actions).isSome = true ↔
        Host.replayCertified world goal cap actions = true) :=
  ⟨fun _ _ _ _ _ => dite_isSome _⟩

/-- Blocked checking returns a certificate exactly when the blocked checker accepts the
region. The certificate's type carries that acceptance; `AcornVerif.Decisions.region_blocked`
states what it establishes. -/
theorem blocked_check : Regula.ExecutableContract Host.BlockedCertificate.check (fun check =>
    ∀ (config : Host.WorldConfig) (boat : Bool) (target start : Host.Position)
      (cells : List Host.Position),
      (check config boat target start cells).isSome = true ↔
        Host.regionBlocked config boat target cells start = true) :=
  ⟨fun _ _ _ _ _ => dite_isSome _⟩

/-- Stance checking returns a certificate exactly when the stance checker accepts the stance.
The certificate's type carries that acceptance; `AcornVerif.Decisions.stance_certified` states
what it establishes. -/
theorem stance_check : Regula.ExecutableContract Host.StanceCertificate.check (fun check =>
    ∀ (config : Host.WorldConfig) (item : Host.Item) (stance : Host.BoxPosition config)
      (direction : Host.Direction),
      (check config item stance direction).isSome = true ↔
        Host.stanceCertified config stance direction item = true) :=
  ⟨fun _ _ _ _ => dite_isSome _⟩

end Acorn.Decisions
