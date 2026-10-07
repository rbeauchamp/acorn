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
import Acorn.Host.Viewer.BrowserStore
import Acorn.Host.Viewer.ControlRequest
import Acorn.Host.Viewer.GoalProtocol
import Acorn.Host.Viewer.Options
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

A decision is registered when a theorem beside its definition, or in the proof library, proves
a property of its accepted or refused results, or when the inputs it accepts follow by
unfolding its definition in this module. The property is the set of accepted or refused inputs
where a theorem states one, and otherwise what an accepted or a refused result is; each
contract's docstring says which. A contract states only what its theorem proves: a decision
with one proved direction carries that direction alone. Six groups are registered.

* Decisions of independent arguments carry a kind and the registration. A function of several
  arguments is decided on their product through `Function.uncurry`.
* A decision procedure whose result type is `Decidable _` carries both directions in its type,
  so it is registered with no contract.
* A decision with an argument or result type that depends on an earlier argument, such as
  `Bounded32.admit`, has no kind: a kind is stated about a function between two fixed types.
  The proved statement is registered as a requirement with no kind, and the function carries
  no `@[regula_decision]` registration. The ownership audit requires each such contract by
  name instead, with a statement that still refers to the executing definition.
* A decision that takes its element type as an argument, such as `Host.Viewer.Buffer.offer`,
  has no kind for the same reason, and its statement for every element type is registered in
  the same way.
* A function between fixed types has no kind when no theorem states a set of the inputs that
  it accepts. `Host.terrain` is the one such function: its statement, in
  `AcornVerif.Decisions`, is about what the readers of its result do with it. The proved
  statement is registered as a requirement with no kind, and the ownership audit requires it
  in the same way.
* A function with a kind can carry a second statement beside it for what its kind does not
  state: the value of an accepted result (`cli_value_found`), or the exact verdict on a part
  of the inputs (`capture_follows`, and `task_observed` in `AcornVerif.Decisions`). That
  statement is a requirement with no kind, and the ownership audit requires it by name.

A requirement with no kind is a statement that the Regula audit does not examine: that audit
checks only that its theorem is proved about the executing definition. Such a statement can
fix one direction only, and no statement here shows that both outcomes occur for its function.
Each docstring says what its statement gives and what it does not claim. Kinds for these
functions are remaining work of https://github.com/rbeauchamp/acorn/issues/67.

A contract whose proof needs the proof library is stated in `AcornVerif.Decisions`. Regula
counts only a contract of the function's own library toward a registration, so such a function
is not registered here, and the ownership audit requires its contract in the same way. The
certificate checkers `Host.replayCertified`, `Host.regionBlocked` and `Host.stanceCertified`
are stated there, with `Host.walkableTile`: what an accepted certificate establishes is a
statement about runs of the executed world step, proved in `AcornVerif.CurrentCertificates`.
No checker is complete, so `Host.regionBlocked` carries the sound kind and the other two, whose
arguments have a dependent type, a requirement with no kind. `Host.walkableTile` carries the
two-way kind.

## What is not registered

The groups below are a list with no check of completeness: a new definition with a `Bool`,
`Option`, `Except` or `Decidable _` result can arrive with no contract and no entry here. A
report of the definitions that have no contract is work of Regula
(https://github.com/rbeauchamp/regula/issues/115).

* A structure field, which is stored data, and a function with a `Decidable _` result, which
  carries both directions of its decision in its type, have no contract.
* No theorem of the maintained libraries names the definition in its statement. This is the
  absence of a direct reference and nothing more. These are the command-line parsers of
  `Host.Cli`, `Host.AgentArguments`, the native drivers and `NativeApp`, the JSON parser
  `Json.parse` with its readers and private helpers, the viewer's envelope and map decoders,
  and the transitions and lookups that no theorem mentions. Kinds for the parsers against
  written grammars are the subject of https://github.com/rbeauchamp/acorn/issues/81. Most are
  functions between fixed types, `Host.Viewer.MapBytes.admit` and `Host.Viewer.decodeMapRuns`
  return `Except String (MapBytes key)` for the receiving key, and `Json.decode` returns
  `Except String α` for the result type `α` it is given.
* No theorem names the definition, and its body applies a definition that has a contract or a
  `Decidable _` result. `Prediction.admit` and `LogStepSize.admit` are `Bounded32.admit` at
  a derived interval, `Lifetime.SumCount.admit` is the body of `Checkpoint.admitSum`, the
  viewer's line emitters apply `wireText` and `sseLine`, and `Host.CertificateDriver.execute`
  refuses when `Host.WorldConfig.standard` or world generation does.
* No theorem names the definition, it belongs to `Host.CertificateSearch`, and each caller
  outside that module applies a definition that has a contract or a `Decidable _` result.
* The definition is the comparison of an instance that a `deriving` clause generated.
* The definition is the default value of a structure field that is not a function, which is
  stored data as the field is.
* The definition belongs to the proof library `AcornVerif`, which has no executable. Its
  theorems relate it to the executing definitions, and no claim rests on running it. The
  interaction kernel and the world classes (`AcornVerif.Kernel`, `AcornVerif.WorldClass`) state
  worlds, agents, goals and bounds as structures and propositions, so they declare no
  definition with such a result.
* A theorem names the definition and no contract states it. These are transitions of the
  world, of the attempt and campaign runners, of the temporal controller and of the agent
  prefix, and selections and predicates of the feature library. This module makes no
  statement about what a caller does with the result of such a definition. The draw-first
  dispatch of the step order `act-then-learn` (`Handcrafted.TemporalControl.drawFirst`) is in
  this group, as selection is: it returns no state when a declared potential has no source,
  and `Handcrafted.TemporalControl.drawFirst_total` states that it returns one from every
  aligned state.

The body of a registered decision applies some of these definitions, directly or through
other definitions. Where a theorem names such a definition, it has a contract; a section near
the end of this module states those. One definition is the exception:
`AgentConstruction.State.restore`, which `Checkpoint.load` applies, is the restoration of the
agent on the admitted image (`AgentConstruction.State.restore_agent`), and the restoration of
the agent has the contract `agent_restore`. Where no theorem names an applied definition, it
has no contract of its own, and the contract of the decision that applies it is the evidence.

What the list does not hold:

* This module cannot register a function of `NativeApp`: Regula counts only a contract of the
  function's own library and refuses a registration written for a declaration of another.
  Each is in the group that no theorem names. `Bootstrap` decides only in `IO`.
* An effect is not in the list: its result type is `IO`. An effect with a pure core is
  covered through that core. `Checkpoint.loadFile` returns the verdict of `Checkpoint.load` on
  the bytes it read, `Checkpoint.Store.save` refuses with `Checkpoint.saveBytes`, and
  `Host.CertificateDriver.dispatch` admits its arguments with `Host.CertificateDriver.natural`
  and `Host.Coordinate.checked` and prints what `execute` returns. An effect with no pure core
  decides from state outside the Lean definitions, so no theorem states its verdict:
  `Host.StopFlag.requested` and the `Host.Viewer.Broadcast` operations read shared state under
  a lock, `Host.Viewer.RunDirectory.adoptStrayCheckpoint` reads the file system and
  `Host.Viewer.NativeResources.observe` reads the operating system. The concurrency and
  operating-system assumptions of the verification guide stand for them.
* The gates under `lean/AcornTools` are outside the Regula claim as reviewed tooling. Their
  pure checks, such as `AcornNativeAudit.allowedArgument`, are part of that trust boundary.

No kind says that a specification is the intended one, that every caller acts on the verdict,
or which value an accepting result carries. Exactness of the accepted value is stated by the
theorems beside each definition.

This module declares theorems, specification predicates and two closed values, `wide` and
`last`, which are the inputs of the witnesses of one kind.
No executable and no other module imports it, so no entry point links those definitions, and
the registration attribute's module, which imports Lean's elaborator, is linked into no
native entry point.
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

/-! ## Closed inputs of the terrain kind

`tile_impassable` states a two-way kind, and a kind carries one accepted and one refused
input. Each value below is closed: it names no variable, and the kernel evaluates the terrain
at it. -/

/-- A world configuration whose box reaches the last coordinate, with a noise scale of one.
The kernel evaluates the terrain of its tiles at that scale, so a tile of this configuration
is the accepted input of `tile_impassable`. -/
def wide : Host.WorldConfig :=
  ⟨⟨0, ⟨2 ^ 63 - 1, by decide⟩, 1, 0, 0, 0, 0, ⟨0x3f800000⟩⟩, by decide, by decide⟩

/-- The position with the last horizontal coordinate. The terrain generator refuses it with a
coordinate overflow, and the kernel evaluates that refusal. -/
def last : Host.Position := ⟨⟨2 ^ 63 - 1, by decide⟩, ⟨0, by decide⟩⟩

/-- An admission that is one test with a computed value accepts exactly when the tested
condition holds. -/
private theorem ite_isSome.{u} {α : Type u} {condition : Prop} [Decidable condition]
    (value : α) : (if condition then some value else none).isSome = true ↔ condition := by
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

/-- A binary32 word is not a NaN exactly when its magnitude does not exceed infinity's. -/
private theorem ordered32 (word : Binary32) :
    word.isNaN = false ↔ word.magnitude ≤ 0x7f800000 := by
  rw [Binary32.isNaN_eq_magnitude, decide_eq_false_iff_not, Nat.not_lt]

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

/-- Strict word comparison accepts exactly two words with a magnitude of infinity's or less in
strict signed-key order
(`Binary32.less_eq_key`). -/
theorem binary32_less : Regula.ExecutableContract Binary32.less (fun compare =>
    Regula.Decides (· = true)
      (fun words : Binary32 × Binary32 =>
        words.1.magnitude ≤ 0x7f800000 ∧ words.2.magnitude ≤ 0x7f800000 ∧
          words.1.key < words.2.key)
      (Function.uncurry compare)) :=
  ⟨decides
    (fun words => by
      show words.1.less words.2 = true ↔ _
      rw [Binary32.less_eq_key, ← ordered32, ← ordered32]
      simp [and_assoc])
    ⟨(.zero, ⟨0x3f800000⟩), by decide⟩ ⟨(.zero, .zero), by decide⟩⟩

attribute [regula_decision] Binary32.less

/-- Non-strict word comparison accepts exactly two words with a magnitude of infinity's or less
in signed-key order
(`Binary32.lessOrEqual_eq_key`). -/
theorem binary32_less_or_equal : Regula.ExecutableContract Binary32.lessOrEqual (fun compare =>
    Regula.Decides (· = true)
      (fun words : Binary32 × Binary32 =>
        words.1.magnitude ≤ 0x7f800000 ∧ words.2.magnitude ≤ 0x7f800000 ∧
          words.1.key ≤ words.2.key)
      (Function.uncurry compare)) :=
  ⟨decides
    (fun words => by
      show words.1.lessOrEqual words.2 = true ↔ _
      rw [Binary32.lessOrEqual_eq_key, ← ordered32, ← ordered32]
      simp [and_assoc])
    ⟨(.zero, .zero), by decide⟩ ⟨(⟨0x3f800000⟩, .zero), by decide⟩⟩

attribute [regula_decision] Binary32.lessOrEqual

/-- Numeric word equality accepts exactly two words with a magnitude of infinity's or less and
equal signed keys
(`Binary32.numericallyEqual_eq_key`). -/
theorem binary32_equal : Regula.ExecutableContract Binary32.numericallyEqual (fun compare =>
    Regula.Decides (· = true)
      (fun words : Binary32 × Binary32 =>
        words.1.magnitude ≤ 0x7f800000 ∧ words.2.magnitude ≤ 0x7f800000 ∧
          words.1.key = words.2.key)
      (Function.uncurry compare)) :=
  ⟨decides
    (fun words => by
      show words.1.numericallyEqual words.2 = true ↔ _
      rw [Binary32.numericallyEqual_eq_key, ← ordered32, ← ordered32]
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

/-- A binary64 word is not a NaN exactly when its magnitude does not exceed infinity's. -/
private theorem ordered64 (word : Binary64) :
    word.isNaN = false ↔ word.magnitude ≤ 0x7ff0000000000000 := by
  have classified : word.isNaN = true ↔ word.magnitude > 0x7ff0000000000000 :=
    decide_eq_true_iff
  rw [← Bool.not_eq_true, classified, Nat.not_lt]

/-- Strict binary64 comparison accepts exactly two words with a magnitude of infinity's or
less in strict signed-key order (`Binary64.less_eq_key`). -/
theorem binary64_less : Regula.ExecutableContract Binary64.less (fun compare =>
    Regula.Decides (· = true)
      (fun words : Binary64 × Binary64 =>
        words.1.magnitude ≤ 0x7ff0000000000000 ∧ words.2.magnitude ≤ 0x7ff0000000000000 ∧
          words.1.key < words.2.key)
      (Function.uncurry compare)) :=
  ⟨decides
    (fun words => by
      show words.1.less words.2 = true ↔ _
      rw [Binary64.less_eq_key, ← ordered64, ← ordered64]
      simp [and_assoc])
    ⟨(⟨0⟩, ⟨0x3ff0000000000000⟩), by decide⟩ ⟨(⟨0⟩, ⟨0⟩), by decide⟩⟩

attribute [regula_decision] Binary64.less

/-- The sign classification accepts exactly the words whose sign bit is set. -/
theorem binary32_negative : Regula.ExecutableContract Binary32.negative
    (Regula.Decides (· = true) (fun word : Binary32 => word.bits &&& 0x80000000 ≠ 0)) :=
  ⟨decides (fun word => by simp [Binary32.negative]) ⟨⟨0x80000000⟩, by decide⟩
    ⟨.zero, by decide⟩⟩

attribute [regula_decision] Binary32.negative

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

/-- A resumable profile, stated by its four discriminants: the profile whose state a
checkpoint holds. -/
def Resumable (profile : FeatureProfile) : Prop :=
  profile.mode = .final ∧ profile.credit = .perStep ∧ profile.rate = .declared ∧
    profile.subtasks = .learned

/-- The executed resumable-profile test accepts exactly a resumable profile. -/
private theorem resumable_iff (profile : FeatureProfile) :
    profile.checkpointSupported = true ↔ Resumable profile :=
  FeatureProfile.checkpoint_iff profile


/-- Agent construction accepts exactly a nonzero tiling word, a bank of one to 65535 units
and a capacity exponent below 32, under each step order (`AgentConstruction.admit_iff`). -/
theorem agent_construction_admit :
    Regula.ExecutableContract AgentConstruction.admit (fun admit =>
      Regula.Decides (·.isSome = true)
        (fun input : ((((((FeatureProfile × Criterion) × PlanningSelection) × StepOrder) ×
            UInt64) × UInt64) × Nat) × Nat =>
          0 < input.1.1.2.toNat ∧ 0 < input.1.2 ∧ input.1.2 ≤ 65535 ∧ input.2 < 32)
        (Function.uncurry (Function.uncurry (Function.uncurry (Function.uncurry
          (Function.uncurry (Function.uncurry (Function.uncurry admit)))))))) :=
  ⟨decides
    (fun input => AgentConstruction.admit_iff input.1.1.1.1.1.1.1 input.1.1.1.1.1.1.2
      input.1.1.1.1.1.2 input.1.1.1.1.2 input.1.1.1.2 input.1.1.2 input.1.2 input.2)
    ⟨(((((((⟨.final, .perStep, .declared, .learned⟩, .discounted), .expectation),
        .learnThenAct), 0), 1), 1), 0),
      by decide⟩
    ⟨(((((((⟨.final, .perStep, .declared, .learned⟩, .discounted), .expectation),
        .learnThenAct), 0), 0), 1), 0),
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

/-- The specification of header admission, over a receiving construction and a header: some
reward rate meets every condition of `Checkpoint.HeaderAdmitted`. That structure states the
header's generation, criterion, reward rate, shape, seed, representation and step order on
the stored words and the typed values, and it calls no function that the admission
executes. -/
def HeaderMatches (input : AgentConstruction × Checkpoint.Header) : Prop :=
  ∃ gain : RewardRate, Checkpoint.HeaderAdmitted input.1 input.2 gain

/-- Header admission returns a reward rate exactly for a header that matches its receiver
(`Checkpoint.admitHeader_iff`). -/
private theorem admitHeader_isOk (construction : AgentConstruction) (header : Checkpoint.Header) :
    (Checkpoint.admitHeader construction header).isOk = true ↔
      HeaderMatches (construction, header) := by
  unfold HeaderMatches
  constructor
  · intro accepted
    cases admitted : Checkpoint.admitHeader construction header with
    | error refusal =>
      rw [admitted] at accepted
      exact absurd accepted Bool.false_ne_true
    | ok gain => exact ⟨gain, (Checkpoint.admitHeader_iff construction header gain).mp admitted⟩
  · rintro ⟨gain, specified⟩
    rw [(Checkpoint.admitHeader_iff construction header gain).mpr specified]
    rfl

/-- Header admission accepts exactly the headers that name the receiving construction's
generation, criterion, shape, seed, resumable profile, representation and step order, with a
reward rate in its interval (`Checkpoint.admitHeader_iff`). -/
theorem header_admit : Regula.ExecutableContract Checkpoint.admitHeader (fun admit =>
    Regula.Decides (·.isOk = true) HeaderMatches (Function.uncurry admit)) :=
  ⟨decides (fun input => admitHeader_isOk input.1 input.2)
    ⟨(AgentConstruction.standard 0 ⟨.ranked, .discounted⟩ .expectation .learnThenAct,
        ⟨Checkpoint.formatVersion, Acorn.FeatureConstants.defaultWeightSpace.toUInt32,
          Checkpoint.primaryCount.toUInt32, 0, 0, 0, .zero,
          Acorn.FeatureConstants.defaultTilings.toUInt64,
          Acorn.FeatureConstants.defaultImprintUnits.toUInt32, 1, 0⟩),
      (admitHeader_isOk _ _).mp (by decide)⟩
    ⟨(AgentConstruction.standard 0 ⟨.ranked, .discounted⟩ .expectation .learnThenAct,
        ⟨Checkpoint.formatVersion + 1, 0, 0, 0, 0, 0, .zero, 0, 0, 0, 0⟩),
      fun ⟨_, specified⟩ => absurd specified.version (by decide)⟩⟩

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

/-- The derived comparison of an action with the harvest action accepts exactly the harvest
action. -/
private theorem harvest_beq (action : Host.Action) :
    (action == .harvest) = true ↔ action = .harvest := by
  cases action <;>
    first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun same => absurd same (by decide), fun same => nomatch same⟩

/-- The raw energy cost is accepted exactly when the product fits 32 bits: the multiplier
times the harvest cost for the harvest action, and the multiplier for every other action
(`Host.Action.rawEnergyCost_exact`). The specification states the action by constructor
equality and names no comparison. -/
theorem raw_energy_cost : Regula.ExecutableContract Host.Action.rawEnergyCost (fun cost =>
    Regula.Decides (·.isSome = true)
      (fun input : Host.Action × UInt32 =>
        (input.1 = .harvest → Acorn.FeatureConstants.harvestCost * input.2.toNat < 2 ^ 32) ∧
          (input.1 ≠ .harvest → input.2.toNat < 2 ^ 32))
      (Function.uncurry cost)) :=
  ⟨decides
    (fun ⟨action, multiplier⟩ => by
      show (Host.Action.rawEnergyCost action multiplier).isSome = true ↔ _
      unfold Host.Action.rawEnergyCost
      dsimp only
      rw [ite_isSome]
      by_cases harvest : action = .harvest
      · rw [ite_eq_left ((harvest_beq action).mpr harvest)]
        exact ⟨fun fits => ⟨fun _ => fits, fun differs => absurd harvest differs⟩,
          fun both => both.1 harvest⟩
      · have test : ¬(action == .harvest) = true := fun same =>
          harvest ((harvest_beq action).mp same)
        rw [ite_eq_right test, Nat.one_mul]
        exact ⟨fun fits => ⟨fun same => absurd same harvest, fun _ => fits⟩,
          fun both => both.2 harvest⟩)
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

/-- The option reader accepts exactly when the first occurrence of the option is not the last
argument (`Host.Cli.value_missing`). -/
private theorem value_accepts (arguments : List String) (wanted : String) :
    (Host.Cli.value arguments wanted).isOk = true ↔ ¬Host.Cli.Ends arguments wanted := by
  cases found : Host.Cli.value arguments wanted with
  | error refusal =>
    have ends := ((Host.Cli.value_missing arguments wanted refusal).mp found).1
    exact ⟨fun accepted => absurd accepted Bool.false_ne_true, fun follows => absurd ends follows⟩
  | ok result =>
    refine ⟨fun _ ends => ?_, fun _ => rfl⟩
    have refused := (Host.Cli.value_missing arguments wanted (.missing wanted)).mpr ⟨ends, rfl⟩
    rw [found] at refused
    cases refused

/-- Planning admission from an argument list accepts exactly a list without the option, or one
whose first occurrence of the option has a canonical spelling after it
(`Host.Cli.planningSelection_absent`, `Host.Cli.planningSelection_provided`). A missing value
is refused. The specification is stated on the argument list and names no reader. -/
theorem planning_selection : Regula.ExecutableContract Host.Cli.planningSelection
    (Regula.Decides (·.isOk = true) (fun arguments : List String =>
      "--planning" ∉ arguments ∨
        ∃ selection,
          Host.Cli.Follows arguments "--planning" (PlanningSelection.name selection))) :=
  ⟨.of_iff
    (fun arguments => by
      show (Host.Cli.planningSelection arguments).isOk = true ↔ _
      have present := Host.Cli.value_follows arguments "--planning"
      rw [← Host.Cli.value_absent arguments "--planning"]
      cases found : Host.Cli.value arguments "--planning" with
      | error refusal =>
        have refused : (Host.Cli.planningSelection arguments).isOk = false := by
          simp [Host.Cli.planningSelection, found, Except.isOk, Except.toBool, bind, Except.bind]
        rw [refused]
        constructor
        · intro accepted
          cases accepted
        · rintro (absurd | ⟨selection, first⟩)
          · cases absurd
          · have provided := (present _).mpr first
            rw [found] at provided
            cases provided
      | ok text =>
        cases text with
        | none =>
          simp [Host.Cli.planningSelection_absent arguments found, Except.isOk, Except.toBool]
        | some text =>
          rw [Host.Cli.planningSelection_provided arguments text found, planningValue_isOk]
          constructor
          · intro accepted
            obtain ⟨selection, written⟩ := (planning_parse.evidence.iff text).mp accepted
            have first := (present text).mp found
            exact .inr ⟨selection, written ▸ first⟩
          · rintro (absurd | ⟨selection, first⟩)
            · cases absurd
            · have provided := (present _).mpr first
              rw [found] at provided
              have written : text = PlanningSelection.name selection := by simpa using provided
              exact (planning_parse.evidence.iff text).mpr ⟨selection, written⟩)
    ⟨[], by decide⟩ ⟨["--planning"], by decide⟩⟩

attribute [regula_decision] Host.Cli.planningSelection

/-- Step-order parsing returns an order exactly for a text that spells one
(`StepOrder.parse_spelled`). -/
private theorem stepOrderParse_isSome (text : String) :
    (StepOrder.parse text).isSome = true ↔ ∃ order, StepOrder.Spelled text order := by
  constructor
  · intro accepted
    cases parsed : StepOrder.parse text with
    | none =>
      rw [parsed] at accepted
      exact absurd accepted Bool.false_ne_true
    | some order => exact ⟨order, (StepOrder.parse_spelled text order).mp parsed⟩
  · rintro ⟨order, spelled⟩
    rw [(StepOrder.parse_spelled text order).mpr spelled]
    rfl

/-- Step-order parsing accepts exactly the texts that spell one of the three step orders
(`StepOrder.parse_spelled`, `StepOrder.parse_refused`). The specification, `StepOrder.Spelled`,
is written on the three words and calls no function that the parser executes. -/
theorem step_order_parse : Regula.ExecutableContract StepOrder.parse
    (Regula.Decides (·.isSome = true) (fun text => ∃ order, StepOrder.Spelled text order)) :=
  ⟨decides stepOrderParse_isSome ⟨"act-then-learn", .actThenLearn, .inr (.inr ⟨rfl, rfl⟩)⟩
    ⟨"", fun specified => absurd ((stepOrderParse_isSome "").mpr specified) (by decide)⟩⟩

attribute [regula_decision] StepOrder.parse

/-- The command-line step-order value is accepted exactly when the shared parser accepts it. -/
private theorem stepOrderValue_isOk (text : String) :
    (Host.Cli.stepOrderValue text).isOk = (StepOrder.parse text).isSome := by
  unfold Host.Cli.stepOrderValue
  cases StepOrder.parse text <;> rfl

/-- Command-line step-order admission accepts exactly the texts that spell one of the three
step orders, through the shared parser and with no substitution
(`Host.Cli.stepOrderValue_iff`, `Host.Cli.stepOrderValue_refused`). -/
theorem step_order_value : Regula.ExecutableContract Host.Cli.stepOrderValue
    (Regula.Decides (·.isOk = true) (fun text => ∃ order, StepOrder.Spelled text order)) :=
  ⟨decides
    (fun text => by
      show (Host.Cli.stepOrderValue text).isOk = true ↔ _
      rw [stepOrderValue_isOk]
      exact step_order_parse.evidence.iff text)
    step_order_parse.evidence.toDecidesSoundly.satisfiable
    step_order_parse.evidence.toDecidesCompletely.refutable⟩

attribute [regula_decision] Host.Cli.stepOrderValue

/-- Step-order admission from an argument list returns an order exactly for a list without
the option, or one whose first occurrence of the option is followed by a text that spells an
order (`Host.Cli.stepOrder_iff`). -/
private theorem stepOrder_isOk (arguments : List String) :
    (Host.Cli.stepOrder arguments).isOk = true ↔
      "--step-order" ∉ arguments ∨
        ∃ text order, Host.Cli.Follows arguments "--step-order" text ∧
          StepOrder.Spelled text order := by
  constructor
  · intro accepted
    cases admitted : Host.Cli.stepOrder arguments with
    | error refusal =>
      rw [admitted] at accepted
      exact absurd accepted Bool.false_ne_true
    | ok order =>
      rcases (Host.Cli.stepOrder_iff arguments order).mp admitted with ⟨absent, _⟩ |
        ⟨text, follows, spelled⟩
      · exact .inl absent
      · exact .inr ⟨text, order, follows, spelled⟩
  · rintro (absent | ⟨text, order, follows, spelled⟩)
    · rw [(Host.Cli.stepOrder_iff arguments .learnThenAct).mpr (.inl ⟨absent, rfl⟩)]
      rfl
    · rw [(Host.Cli.stepOrder_iff arguments order).mpr (.inr ⟨text, follows, spelled⟩)]
      rfl

/-- Step-order admission from an argument list accepts exactly a list without the option, or
one whose first occurrence of the option is followed by a text that spells one of the three
step orders (`Host.Cli.stepOrder_iff`, `Host.Cli.stepOrder_refused`). A missing value is
refused. The specification is stated on the argument list and names no reader. -/
theorem step_order : Regula.ExecutableContract Host.Cli.stepOrder
    (Regula.Decides (·.isOk = true) (fun arguments : List String =>
      "--step-order" ∉ arguments ∨
        ∃ text order, Host.Cli.Follows arguments "--step-order" text ∧
          StepOrder.Spelled text order)) :=
  ⟨decides stepOrder_isOk ⟨[], .inl (by decide)⟩
    ⟨["--step-order"], fun specified =>
      absurd ((stepOrder_isOk ["--step-order"]).mpr specified) (by decide)⟩⟩

attribute [regula_decision] Host.Cli.stepOrder

/-- The option reader refuses exactly when the first occurrence of the option is the last
argument, so that no value stands after it (`Host.Cli.value_missing`). The specification
`Host.Cli.Ends` is stated on the argument list. `cli_value_found` states which value an
accepted result carries. -/
theorem cli_value : Regula.ExecutableContract Host.Cli.value (fun value =>
    Regula.Decides (·.isOk = true)
      (fun input : List String × String => ¬Host.Cli.Ends input.1 input.2)
      (Function.uncurry value)) :=
  ⟨.of_iff (fun input => value_accepts input.1 input.2) ⟨([], ""), by decide⟩
    ⟨([""], ""), by decide⟩⟩

attribute [regula_decision] Host.Cli.value

/-- The option reader returns no value exactly for a list without the option, and it returns a
value exactly when that value stands after the first occurrence of the option
(`Host.Cli.value_absent`, `Host.Cli.value_follows`). A kind states the accepted inputs and
not the value of a result, so this statement is a requirement with no kind beside the kind
`cli_value`. -/
theorem cli_value_found : Regula.ExecutableContract Host.Cli.value (fun value =>
    ∀ (arguments : List String) (wanted : String),
      (value arguments wanted = .ok none ↔ wanted ∉ arguments) ∧
        ∀ text, value arguments wanted = .ok (some text) ↔
          Host.Cli.Follows arguments wanted text) :=
  ⟨fun arguments wanted =>
    ⟨Host.Cli.value_absent arguments wanted, Host.Cli.value_follows arguments wanted⟩⟩

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

The checkers of `Host.Certificate` decide a certificate by these tests of one tile. The contracts
of the checkers themselves are stated in `AcornVerif.Decisions`, with what an accepted
certificate establishes. -/

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
when the certificate is for a body without a boat. It refuses a terrain refusal. The terrain
generator is the subject of the claim: the specification names `Host.terrain`, which the test
reads. The accepted input is a tile of the wide world for a body without a boat, and the
refused input is the last coordinate, whose terrain the generator refuses. -/
theorem tile_impassable : Regula.ExecutableContract Host.impassable (fun test =>
    Regula.Decides (· = true)
      (fun input : (Host.WorldConfig × Bool) × Host.Position =>
        Host.terrain input.2 input.1.1.raw.seed input.1.1.raw.baseScale = .ok .mountain ∨
          (Host.terrain input.2 input.1.1.raw.seed input.1.1.raw.baseScale = .ok .water ∧
            input.1.2 = false))
      (Function.uncurry (Function.uncurry test))) :=
  ⟨.of_iff
    (fun ⟨⟨config, boat⟩, tile⟩ => by
      show Host.impassable config boat tile = true ↔ _
      unfold Host.impassable
      cases Host.terrain tile config.raw.seed config.raw.baseScale with
      | error refusal => simp
      | ok kind => cases kind <;> simp)
    ⟨((wide, false), ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩), by decide +kernel⟩
    ⟨((wide, true), last), by decide +kernel⟩⟩

attribute [regula_decision] Host.impassable

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

/-- The fitting test accepts exactly: the identity conversion of every shape, a float
conversion of a binary32 or binary64 shape, an optional-reading or optional-index conversion
of an optional natural, and each array conversion of an array of its own element shape
(`TelemetryShape.defaultConversion_fits` and `browserConversion_fits` state that it accepts the
default conversion and the conversion that the browser schema assigns). -/
theorem conversion_fits : Regula.ExecutableContract BrowserConversion.fits (fun test =>
    Regula.Decides (· = true)
      (fun input : BrowserConversion × TelemetryShape =>
        input.1 = .keep ∨
          (input.1 = .nonFinite ∧ (input.2 = .binary32 ∨ input.2 = .binary64)) ∨
          ((input.1 = .unmeasured ∨ input.1 = .absentIndex) ∧ input.2 = .optional .natural) ∨
          ∃ count, (input.1 = .float32 ∧ input.2 = .array count .binary32) ∨
            (input.1 = .float64 ∧ input.2 = .array count .binary64) ∨
            (input.1 = .counts ∧ input.2 = .array count .natural) ∨
            (input.1 = .absentIndices ∧ input.2 = .array count (.optional .natural)))
      (Function.uncurry test)) :=
  ⟨decides
    (fun ⟨conversion, shape⟩ => by
      cases conversion <;> cases shape <;>
        first
        | (simp [Function.uncurry, BrowserConversion.fits]; done)
        | (rename_i element
           cases element <;>
             first
             | (simp [Function.uncurry, BrowserConversion.fits]; done)
             | (rename_i inner
                cases inner <;> simp [Function.uncurry, BrowserConversion.fits])))
    ⟨(.keep, .natural), .inl rfl⟩ ⟨(.nonFinite, .natural), by simp⟩⟩

attribute [regula_decision] BrowserConversion.fits

/-- The exclusive bound that the browser rules place on the present indices of a field: the
bound of the first rule that gives the key an array of optional bounded indices. Stated on the
rule table, with no lookup. -/
def FirstIndexBound (key : String) (upper : Nat) : Prop :=
  ∃ before after,
    browserRules = before ++ (key, BrowserRule.each (.nullable (.range upper))) :: after ∧
      ∀ other, (key, BrowserRule.each (.nullable (.range other))) ∉ before

private theorem indexBound_iff (key : String) (upper : Nat) :
    browserIndexBound key = some upper ↔ FirstIndexBound key upper := by
  unfold browserIndexBound FirstIndexBound
  rw [List.findSome?_eq_some_iff]
  constructor
  · rintro ⟨before, ⟨name, rule⟩, after, parts, found, absent⟩
    dsimp only at found
    split at found
    · rename_i bound
      by_cases same : name = key
      · subst same
        simp only [↓reduceIte, Option.some.injEq] at found
        subst found
        refine ⟨before, after, parts, fun other member => ?_⟩
        have none := absent _ member
        simp at none
      · simp [same] at found
    · simp at found
  · rintro ⟨before, after, parts, absent⟩
    refine ⟨before, _, after, parts, by simp, fun ⟨name, rule⟩ member => ?_⟩
    dsimp only
    split
    · rename_i bound
      by_cases same : name = key
      · subst same
        exact absurd member (absent bound)
      · simp [same]
    · rfl

/-- The index-range test accepts exactly: every conversion that is not an index array, and an
index array under a key whose first optional-index rule bounds each present index by `2 ^ 31`
or less (`TelemetryShape.defaultConversion_indexed` and `browserConversion_indexed` state that
it accepts the default conversion and the conversion that the browser schema assigns). The
specification `FirstIndexBound` is stated on the rule table and names no lookup. -/
theorem conversion_indexed : Regula.ExecutableContract BrowserConversion.indexed (fun test =>
    Regula.Decides (· = true)
      (fun input : BrowserConversion × String =>
        input.1 = .absentIndices → ∃ upper, FirstIndexBound input.2 upper ∧ upper ≤ 2 ^ 31)
      (Function.uncurry test)) :=
  ⟨.of_iff
    (fun ⟨conversion, key⟩ => by
      show conversion.indexed key = true ↔
        (conversion = .absentIndices → ∃ upper, FirstIndexBound key upper ∧ upper ≤ 2 ^ 31)
      cases conversion with
      | absentIndices =>
        unfold BrowserConversion.indexed
        cases found : browserIndexBound key with
        | none =>
          constructor
          · intro accepted
            cases accepted
          · intro bounded
            obtain ⟨upper, first, -⟩ := bounded rfl
            rw [(indexBound_iff key upper).mpr first] at found
            cases found
        | some upper =>
          constructor
          · intro within _
            exact ⟨upper, (indexBound_iff key upper).mp found, of_decide_eq_true within⟩
          · intro bounded
            obtain ⟨other, first, within⟩ := bounded rfl
            have same := (indexBound_iff key other).mpr first
            rw [found] at same
            cases same
            exact decide_eq_true within
      | _ => simp [BrowserConversion.indexed])
    ⟨(.keep, ""), by decide⟩ ⟨(.absentIndices, ""), by decide +kernel⟩⟩

attribute [regula_decision] BrowserConversion.indexed

/-- The capture order accepts only two different captures (`Capture.after_irreflexive`).

**Not claimed:** completeness. The order is lexicographic and refuses an earlier capture. -/
theorem capture_after : Regula.ExecutableContract Capture.after (fun test =>
    Regula.DecidesSoundly (· = true)
      (fun input : Capture × Capture => input.1 ≠ input.2) (Function.uncurry test)) :=
  ⟨{ sound := fun input accepted same => by
       have later : input.1.after input.2 = true := accepted
       rw [same, Capture.after_irreflexive] at later
       exact Bool.false_ne_true later
     accepted := ⟨(⟨0, 0, 1, 0, 0, false⟩, ⟨0, 0, 0, 0, 0, false⟩), by decide⟩ }⟩

attribute [regula_decision] Capture.after

/-- The retry test accepts only a retry state whose failure count is below the failure
limit (`Retry.exhausted_not_ready`). The specification names the count and no function that
the test calls.

**Not claimed:** completeness. The test also refuses before the retry deadline. -/
theorem retry_ready : Regula.ExecutableContract Retry.ready (fun test =>
    Regula.DecidesSoundly (· = true)
      (fun input : Retry × UInt64 => input.1.count ≠ failureLimit) (Function.uncurry test)) :=
  ⟨{ sound := fun input accepted spent => by
       have ready : input.1.ready input.2 = true := accepted
       have exhausted : input.1.exhausted = true := by simp [Retry.exhausted, ← spent, Retry.count]
       rw [Retry.exhausted_not_ready input.1 input.2 exhausted] at ready
       exact absurd ready Bool.false_ne_true
     accepted := ⟨(Retry.initial, 0), by decide⟩ }⟩

attribute [regula_decision] Retry.ready

/-- The exhaustion test accepts exactly a retry state whose failure count is the failure
limit. `Retry.exhausted_not_ready` states that no retry is ready in such a state. -/
theorem retry_exhausted : Regula.ExecutableContract Retry.exhausted
    (Regula.Decides (· = true) (fun retry : Retry => retry.count = failureLimit)) :=
  ⟨decides (fun retry => by simp [Retry.exhausted, Retry.count])
    ⟨((Retry.initial.failed 0 false).failed 0 false).failed 0 false, by decide⟩
    ⟨Retry.initial, by decide⟩⟩

attribute [regula_decision] Retry.exhausted

/-- Aggregation accepts exactly a list in which no channel is missing
(`Agreement.aggregateAll_missing` states the refusal of a missing first channel). -/
theorem aggregate_all : Regula.ExecutableContract Agreement.aggregateAll
    (Regula.Decides (·.isSome = true)
      (fun ratios : List (Option Agreement.Ratio) => ∀ ratio ∈ ratios, ratio.isSome = true)) :=
  ⟨decides
    (fun ratios => by
      induction ratios with
      | nil => simp [Agreement.aggregateAll]
      | cons head tail ih =>
        cases head with
        | none => simp [Agreement.aggregateAll]
        | some ratio => simpa [Agreement.aggregateAll] using ih)
    ⟨[], by simp⟩ ⟨[none], by simp⟩⟩

attribute [regula_decision] Agreement.aggregateAll

/-- The aggregate score is present exactly when the product of the question count and the
denominator is positive. `AcornVerif.CurrentAgreement.aggregate_ratio_value` states its value. -/
theorem aggregate_ratio : Regula.ExecutableContract Agreement.Aggregate.ratio
    (Regula.Decides (·.isSome = true)
      (fun aggregate : Agreement.Aggregate =>
        0 < aggregate.questions * aggregate.denominator)) :=
  ⟨decides (fun _ => dite_isSome _)
    ⟨Agreement.Aggregate.empty.add ⟨0, 1, by decide, by decide⟩, by decide⟩
    ⟨.empty, by decide⟩⟩

attribute [regula_decision] Agreement.Aggregate.ratio

/-- Clear is unavailable exactly under a fixed launch command (`fixed_clear_disabled`). -/
theorem clear_disabled : Regula.ExecutableContract LaunchMode.clearDisabled
    (Regula.Decides (·.isSome = true)
      (fun mode : LaunchMode => ∃ command, mode = .fixed command)) :=
  ⟨decides (fun mode => by cases mode <;> simp [LaunchMode.clearDisabled])
    ⟨.fixed "", "", rfl⟩ ⟨.ranked, by simp⟩⟩

attribute [regula_decision] LaunchMode.clearDisabled

/-- The capture-follow test accepts every pair with equal lifetime clocks whose next capture
is terminal, whose previous capture is not, and whose world clock advanced by one
(`Capture.follows_equal_lifetime`), and it refuses a repeated capture. `capture_follows`
states the exact verdict for equal lifetime clocks.

**Not claimed:** soundness. The test also accepts a later lifetime clock. -/
theorem capture_follows_complete : Regula.ExecutableContract Capture.follows (fun test =>
    Regula.DecidesCompletely (· = true)
      (fun input : Capture × Capture =>
        input.1.lifetime = input.2.lifetime ∧ input.1.terminal = true ∧
          input.2.terminal = false ∧ input.1.world.toNat = input.2.world.toNat + 1)
      (Function.uncurry test)) :=
  ⟨{ complete := fun input ⟨same, terminal, running, advanced⟩ => by
       show input.1.follows input.2 = true
       rw [Capture.follows_equal_lifetime input.1 input.2 same]
       simp [terminal, running, advanced]
     refused := ⟨(⟨0, 0, 0, 0, 0, false⟩, ⟨0, 0, 0, 0, 0, false⟩), by decide⟩ }⟩

attribute [regula_decision] Capture.follows

/-- The capture-follow test, for two captures with the same lifetime clock, is exactly: the
next capture is terminal, the previous one is not, and the world clock advanced by one
(`Capture.follows_equal_lifetime`).

The function is between fixed types and carries the complete kind above. This statement is a
requirement with no kind beside it: it is the exact verdict on the pairs with equal lifetime
clocks, and a kind states one set of accepted inputs over all pairs.

**Not claimed:** its verdict when the lifetime clocks differ. -/
theorem capture_follows : Regula.ExecutableContract Capture.follows (fun test =>
    ∀ next previous : Capture, next.lifetime = previous.lifetime →
      test next previous =
        (next.terminal && !previous.terminal &&
          next.world.toNat == previous.world.toNat + 1)) :=
  ⟨Capture.follows_equal_lifetime⟩

/-- The ownership test accepts exactly a tool whose own flag is set in the inventory. -/
theorem inventory_owns : Regula.ExecutableContract Host.Inventory.owns (fun owns =>
    Regula.Decides (· = true)
      (fun input : Host.Inventory × Host.Craftable =>
        (input.2 = .axe ∧ input.1.axe = true) ∨ (input.2 = .boat ∧ input.1.boat = true))
      (Function.uncurry owns)) :=
  ⟨decides
    (fun ⟨inventory, tool⟩ => by cases tool <;> simp [Function.uncurry, Host.Inventory.owns])
    ⟨(⟨0, 0, 0, 0, true, false⟩, .axe), by decide⟩
    ⟨(⟨0, 0, 0, 0, false, false⟩, .axe), by decide⟩⟩

attribute [regula_decision] Host.Inventory.owns

/-- The harvest table yields an item exactly for a tree, stone or ore tile. -/
theorem harvest_yield : Regula.ExecutableContract Host.TileKind.harvestYield
    (Regula.Decides (·.isSome = true)
      (fun kind : Host.TileKind => kind = .tree ∨ kind = .stone ∨ kind = .ore)) :=
  ⟨decides (fun kind => by cases kind <;> simp [Host.TileKind.harvestYield])
    ⟨.tree, .inl rfl⟩ ⟨.grass, by decide⟩⟩

attribute [regula_decision] Host.TileKind.harvestYield

/-- A checkpoint write is due exactly at a closing boundary or at phase zero of its period.
The accepted input is an admitted writer at phase zero, and the refused input is that
writer advanced once, both at a boundary that does not close. -/
theorem checkpoint_due : Regula.ExecutableContract Host.WritableCheckpoint.due (fun due =>
    Regula.Decides (· = true)
      (fun input : Host.WritableCheckpoint × Bool =>
        input.2 = true ∨ input.1.phase.val = 0)
      (Function.uncurry due)) :=
  ⟨decides (fun input => by simp [Function.uncurry, Host.WritableCheckpoint.due])
    ⟨((Host.WritableCheckpoint.admit "checkpoint" 2 .loaded).get (by decide), false),
      by decide⟩
    ⟨(((Host.WritableCheckpoint.admit "checkpoint" 2 .loaded).get (by decide)).advance, false),
      by decide⟩⟩

attribute [regula_decision] Host.WritableCheckpoint.due

/-- The index-bound lookup finds a bound exactly for a key that the browser rules give an
array of optional bounded indices. -/
theorem index_bound : Regula.ExecutableContract browserIndexBound
    (Regula.Decides (·.isSome = true)
      (fun key : String =>
        ∃ upper, (key, BrowserRule.each (.nullable (.range upper))) ∈ browserRules)) :=
  ⟨.of_iff
    (fun key => by
      unfold browserIndexBound
      rw [List.findSome?_isSome_iff]
      constructor
      · rintro ⟨⟨name, rule⟩, member, found⟩
        dsimp only at found
        split at found
        · rename_i upper
          by_cases same : name = key
          · exact ⟨upper, same ▸ member⟩
          · simp [same] at found
        · simp at found
      · rintro ⟨upper, member⟩
        exact ⟨_, member, by simp⟩)
    ⟨"agreement_channel_score", by decide +kernel⟩ ⟨"", by decide +kernel⟩⟩

attribute [regula_decision] browserIndexBound

/-- The element-bound lookup finds a bound exactly for a key that the browser rules give an
array of bounded elements (`BrowserConstant.tileKinds_admitted` states the bound of the
tiles). -/
theorem element_bound : Regula.ExecutableContract browserElementBound
    (Regula.Decides (·.isSome = true)
      (fun key : String => ∃ upper, (key, BrowserRule.each (.range upper)) ∈ browserRules)) :=
  ⟨.of_iff
    (fun key => by
      unfold browserElementBound
      rw [List.findSome?_isSome_iff]
      constructor
      · rintro ⟨⟨name, rule⟩, member, found⟩
        dsimp only at found
        split at found
        · rename_i upper
          by_cases same : name = key
          · exact ⟨upper, same ▸ member⟩
          · simp [same] at found
        · simp at found
      · rintro ⟨upper, member⟩
        exact ⟨_, member, by simp⟩)
    ⟨"tiles", by decide +kernel⟩ ⟨"", by decide +kernel⟩⟩

attribute [regula_decision] browserElementBound

/-- The numeric-record test accepts exactly: a float conversion of a binary32 or binary64
shape, an optional-reading or optional-index conversion of an optional natural, and the
identity conversion of a natural, an integer, a goal kind or a goal item. -/
theorem conversion_number : Regula.ExecutableContract BrowserConversion.number (fun test =>
    Regula.Decides (· = true)
      (fun input : BrowserConversion × TelemetryShape =>
        (input.1 = .nonFinite ∧ (input.2 = .binary32 ∨ input.2 = .binary64)) ∨
          ((input.1 = .unmeasured ∨ input.1 = .absentIndex) ∧ input.2 = .optional .natural) ∨
          (input.1 = .keep ∧ (input.2 = .natural ∨ input.2 = .integer ∨ input.2 = .goalKind ∨
            input.2 = .goalItem)))
      (Function.uncurry test)) :=
  ⟨decides
    (fun ⟨conversion, shape⟩ => by
      cases conversion <;> cases shape <;>
        first
        | (simp [Function.uncurry, BrowserConversion.number, BrowserConversion.fits]; done)
        | (rename_i element
           cases element <;>
             simp [Function.uncurry, BrowserConversion.number, BrowserConversion.fits]))
    ⟨(.keep, .natural), .inr (.inr ⟨rfl, .inl rfl⟩)⟩ ⟨(.keep, .text), by simp⟩⟩

attribute [regula_decision] BrowserConversion.number

/-- The numeric-array test finds a length exactly for: a binary32 array under the float32
conversion, a binary64 array under the float64 conversion, a natural array under the counts
conversion and an array of optional naturals under the optional-index conversion. -/
theorem conversion_numbers : Regula.ExecutableContract BrowserConversion.numbers (fun test =>
    Regula.Decides (·.isSome = true)
      (fun input : BrowserConversion × TelemetryShape => ∃ count,
        (input.1 = .float32 ∧ input.2 = .array count .binary32) ∨
          (input.1 = .float64 ∧ input.2 = .array count .binary64) ∨
          (input.1 = .counts ∧ input.2 = .array count .natural) ∨
          (input.1 = .absentIndices ∧ input.2 = .array count (.optional .natural)))
      (Function.uncurry test)) :=
  ⟨decides
    (fun ⟨conversion, shape⟩ => by
      cases conversion <;> cases shape <;>
        first
        | (simp [Function.uncurry, BrowserConversion.numbers, BrowserConversion.fits]; done)
        | (rename_i element
           cases element <;>
             first
             | (simp [Function.uncurry, BrowserConversion.numbers, BrowserConversion.fits]; done)
             | (rename_i inner
                cases inner <;>
                  simp [Function.uncurry, BrowserConversion.numbers, BrowserConversion.fits])))
    ⟨(.float32, .array 1 .binary32), 1, .inl ⟨rfl, rfl⟩⟩
    ⟨(.keep, .natural), by simp⟩⟩

attribute [regula_decision] BrowserConversion.numbers

/-- The identity test accepts exactly the generation of a live process, or the last reserved
generation while no process is live (`Lifecycle.ownsIdentity_iff`). The specification
`Lifecycle.OwnsIdentity` is stated on the stored phase and the generation allocator, beside
those private fields, and it names no test. -/
theorem owns_identity :
    Regula.ExecutableContract Host.Viewer.Lifecycle.ownsIdentity (fun owns =>
      Regula.Decides (· = true)
        (fun input : Host.Viewer.Lifecycle × UInt64 => input.1.OwnsIdentity input.2)
        (Function.uncurry owns)) :=
  ⟨.of_iff (fun input => Host.Viewer.Lifecycle.ownsIdentity_iff input.1 input.2)
    ⟨(.initial ⟨0, 0, 0⟩ .stopped, 0), by decide⟩
    ⟨(.initial ⟨0, 0, 0⟩ .stopped, 1), by decide⟩⟩

attribute [regula_decision] Host.Viewer.Lifecycle.ownsIdentity

/-- Each column of the browser store fits each schema field of its own key. -/
private theorem columns_fit : ∀ entry ∈ browserColumns, ∀ field ∈ browserSchema,
    field.1 = entry.1 → BrowserColumn.fits entry.1 entry.2 field.2 = true := by
  decide +kernel

/-- The column test accepts every column of the browser store against the shape that the
browser schema gives its key, and it refuses a flag column against a text shape.

**Not claimed:** soundness. The test accepts columns that the store does not ship. -/
theorem column_fits : Regula.ExecutableContract BrowserColumn.fits (fun fits =>
    Regula.DecidesCompletely (· = true)
      (fun input : (String × BrowserColumn) × TelemetryShape =>
        input.1 ∈ browserColumns ∧ (input.1.1, input.2) ∈ browserSchema)
      (Function.uncurry (Function.uncurry fits))) :=
  ⟨{ complete := fun input listed =>
       columns_fit input.1 listed.1 (input.1.1, input.2) listed.2 rfl
     refused := ⟨(("flag", ⟨"flag", .flag⟩), .text), by decide +kernel⟩ }⟩

attribute [regula_decision] BrowserColumn.fits

/-- A table lookup returns only an item that the table holds. -/
private theorem lookup_listed {β : Type} : ∀ (table : List (String × β)) (key : String) (item : β),
    table.lookup key = some item → ∃ name, (name, item) ∈ table
  | [], _, _, found => by simp at found
  | (name, value) :: rest, key, item, found => by
    rw [List.lookup_cons] at found
    split at found
    · cases found
      exact ⟨name, List.mem_cons_self⟩
    · obtain ⟨other, member⟩ := lookup_listed rest key item found
      exact ⟨other, List.mem_cons_of_mem _ member⟩

/-- The representation of a field is a binary32 array exactly for a binary32 array shape: no
override is defined for such a shape, and only such a shape has that default. -/
private theorem conversion_float32 (key : String) (shape : TelemetryShape) :
    browserConversion key shape = .float32 ↔ ∃ count, shape = .array count .binary32 := by
  have default : shape.defaultConversion = .float32 ↔ ∃ count, shape = .array count .binary32 := by
    cases shape with
    | array count element => cases element <;> simp [TelemetryShape.defaultConversion]
    | _ => simp [TelemetryShape.defaultConversion]
  unfold browserConversion
  cases found : browserOverrides.lookup key with
  | none => exact default
  | some conversion =>
    obtain ⟨name, member⟩ := lookup_listed browserOverrides key conversion found
    have listed : conversion = .unmeasured ∨ conversion = .absentIndex ∨
        conversion = .absentIndices := by
      simp only [browserOverrides, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false]
        at member
      rcases member with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
    show (if conversion.fits shape then conversion else shape.defaultConversion) = .float32 ↔ _
    split
    · rename_i fits
      constructor
      · intro same
        rcases listed with rfl | rfl | rfl <;> cases same
      · rintro ⟨count, rfl⟩
        rcases listed with rfl | rfl | rfl <;> simp [BrowserConversion.fits] at fits
    · exact default

/-- The property test accepts exactly a plain property of any field and a doubled property of
a field with a binary32 array shape (`browserAgreementView_live` and
`browserGoalProgressView_live` state that it accepts the shipped views). The specification is
stated on the reading and the shape, and it names no conversion. -/
theorem property_fits : Regula.ExecutableContract BrowserProperty.fits (fun fits =>
    Regula.Decides (· = true)
      (fun input : (String × BrowserProperty) × TelemetryShape =>
        input.1.2.reading = .value ∨ ∃ count, input.2 = .array count .binary32)
      (Function.uncurry (Function.uncurry fits))) :=
  ⟨decides
    (fun ⟨⟨key, property⟩, shape⟩ => by
      show BrowserProperty.fits key property shape = true ↔
        (property.reading = .value ∨ ∃ count, shape = .array count .binary32)
      unfold BrowserProperty.fits
      cases property.reading with
      | value => simp
      | twice =>
        simp only [reduceCtorEq, false_or]
        rw [← conversion_float32 key shape]
        cases browserConversion key shape <;> simp)
    ⟨(("", ⟨"", .value⟩), .text), .inl rfl⟩
    ⟨(("", ⟨"", .twice⟩), .text), by simp⟩⟩

attribute [regula_decision] BrowserProperty.fits

/-- The phase comparison refuses exactly the idle phase. -/
private theorem phase_live (phase : Host.Viewer.Phase) :
    (phase != .idle) = true ↔ phase ≠ .idle := by
  cases phase with
  | idle => exact ⟨fun differs => absurd differs (by decide), fun differs => absurd rfl differs⟩
  | starting generation => exact ⟨fun _ equal => (nomatch equal), fun _ => rfl⟩
  | running generation => exact ⟨fun _ equal => (nomatch equal), fun _ => rfl⟩
  | stopping generation => exact ⟨fun _ equal => (nomatch equal), fun _ => rfl⟩
  | archiving => exact ⟨fun _ equal => (nomatch equal), fun _ => rfl⟩

/-- The status comparison accepts exactly a failed final save. -/
private theorem status_failed (status : Option Host.CheckpointStatus) :
    (status == some .failed) = true ↔ status = some .failed := by
  cases status with
  | none => exact ⟨fun same => absurd same (by decide), fun same => nomatch same⟩
  | some value =>
    cases value <;>
      first
      | exact ⟨fun _ => rfl, fun _ => rfl⟩
      | exact ⟨fun same => absurd same (by decide), fun same => nomatch same⟩

/-- A control warning is published exactly for an idle lifecycle whose process exited
abnormally or whose final checkpoint save failed (`controlWarning_active` is the refusal while
the lifecycle is not idle). -/
theorem control_warning : Regula.ExecutableContract controlWarning (fun warning =>
    Regula.Decides (·.isSome = true)
      (fun input : Host.Viewer.Lifecycle × ControlDetail =>
        input.1.phaseValue = .idle ∧
          (input.2.abnormalExit = true ∨ input.2.log.checkpoint = some .failed))
      (Function.uncurry warning)) :=
  ⟨.of_iff
    (fun ⟨lifecycle, detail⟩ => by
      show (controlWarning lifecycle detail).isSome = true ↔
        (lifecycle.phaseValue = .idle ∧
          (detail.abnormalExit = true ∨ detail.log.checkpoint = some .failed))
      unfold controlWarning
      by_cases idle : lifecycle.phaseValue = .idle
      · have settled : ¬(lifecycle.phaseValue != .idle) = true := fun differs =>
          (phase_live _).mp differs idle
        rw [ite_eq_right settled]
        by_cases abnormal : detail.abnormalExit = true
        · rw [ite_eq_left abnormal]
          exact ⟨fun _ => ⟨idle, .inl abnormal⟩, fun _ => rfl⟩
        · rw [ite_eq_right abnormal]
          by_cases failed : detail.log.checkpoint = some .failed
          · rw [ite_eq_left ((status_failed _).mpr failed)]
            exact ⟨fun _ => ⟨idle, .inr failed⟩, fun _ => rfl⟩
          · have test : ¬(detail.log.checkpoint == some .failed) = true := fun same =>
              failed ((status_failed _).mp same)
            rw [ite_eq_right test]
            exact ⟨fun present => by simp at present,
              fun cause => cause.2.elim (absurd · abnormal) (absurd · failed)⟩
      · rw [ite_eq_left ((phase_live _).mpr idle)]
        exact ⟨fun present => by simp at present, fun cause => absurd cause.1 idle⟩)
    ⟨(.initial ⟨0, 0, 0⟩ .stopped,
        { transition := .initialized, reason := "", clearDisabled := none, log := {},
          abnormalExit := true }), by decide⟩
    ⟨(.initial ⟨0, 0, 0⟩ .stopped,
        { transition := .initialized, reason := "", clearDisabled := none, log := {} }),
      by decide⟩⟩

attribute [regula_decision] controlWarning

/-! ## Decision procedures

Each result is a `Decidable` value: an accepting result carries a proof of the decided
proposition and a refusing result a proof of its negation, so no contract is registered. The
instances are registered under the names Lean generates for them. -/

attribute [regula_decision] Interval32.orderedDecidable Binary32.positiveDecidable
  Binary32.instDecidableFinite Binary64.instDecidableFinite Interval32.instDecidableContains
  Features.instDecidableRecent Features.instDecidableDominates Lifetime.instDecidableLegalSum
  Checkpoint.instDecidableValid Checkpoint.instDecidableOptionsValid

/-! ## Decisions with a dependent type

An argument or result type of each function below is indexed by an earlier argument: the
receiving interval, the value rule, the feature dimension, the bank configuration or the agent
construction. A decision kind is stated about a function between two fixed types, so none
applies. The proved statement about each function is registered as a requirement with no
kind. Its docstring says what the statement covers: the inputs the function
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
    ∀ config : Acorn.Config, (admit config).isSome = true) :=
  ⟨fun config => Option.isSome_iff_ne_none.mpr (rails_admission_total config)⟩

/-- Squared-discrepancy admission accepts exactly two finite words whose squared discrepancy
is within the squared envelope, and an admitted sample is that exact squared discrepancy
(`Agreement.admitSquared_exact`). `Agreement.squaredUnits` is the measured quantity, which the
admission also computes; `AcornVerif.Decisions.squared_admit_accepts` states acceptance against
the real discrepancy of the two words. -/
theorem squared_admit : Regula.ExecutableContract Agreement.admitSquared (fun admit =>
    ∀ (envelope : Nat) (forecast outcome : Binary32),
      ((admit envelope forecast outcome).isSome = true ↔
        forecast.Finite ∧ outcome.Finite ∧
          Agreement.squaredUnits forecast outcome ≤ envelope ^ 2) ∧
        ∀ sample : Fin (envelope ^ 2 + 1), admit envelope forecast outcome = some sample →
          sample.val = Agreement.squaredUnits forecast outcome) :=
  ⟨fun envelope forecast outcome =>
      ⟨by
        unfold Agreement.admitSquared
        by_cases finite : forecast.Finite ∧ outcome.Finite
        · rw [ite_eq_left finite, dite_isSome, Nat.lt_succ_iff]
          exact ⟨fun within => ⟨finite.1, finite.2, within⟩, fun accepted => accepted.2.2⟩
        · rw [ite_eq_right finite]
          exact ⟨fun accepted => by simp at accepted,
            fun accepted => absurd ⟨accepted.1, accepted.2.1⟩ finite⟩,
        Agreement.admitSquared_exact envelope forecast outcome⟩⟩

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
    (fun checked =>
      ∀ (config : Host.WorldConfig) (position : Host.BoxPosition config),
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

/-- An objective has an identity exactly when it is a selected unit, and the identity is that
unit. -/
private theorem identity_selected {config : Features.Config} (assignment : Assignment config)
    (unit : Fin config.units.count) :
    assignment.identity = some unit ↔ ∃ bonus, assignment = .selected unit bonus := by
  cases assignment with
  | neutral => simp [Assignment.identity]
  | selected other bonus =>
    simp only [Assignment.identity, Option.some.injEq, Assignment.selected.injEq]
    exact ⟨fun same => ⟨bonus, same, rfl⟩, fun ⟨_, same, _⟩ => same⟩

/-- The distinctness test accepts exactly the assignment tables in which no two slots hold a
selected objective of the same unit (`Assignment.distinct_iff`). The specification states the
objectives by their constructor and names no identity reader. -/
theorem assignment_distinct : Regula.ExecutableContract @Assignment.distinct (fun test =>
    ∀ (config : Features.Config)
      (table : Vector (Assignment config) Acorn.FeatureConstants.skillCount),
      @test config table = true ↔
        ∀ (left right : Fin Acorn.FeatureConstants.skillCount) (unit : Fin config.units.count)
          (first second : Bonus), table[left.val] = .selected unit first →
            table[right.val] = .selected unit second → left = right) :=
  ⟨fun config table => by
    rw [Assignment.distinct_iff]
    constructor
    · intro distinct left right unit first second held other
      exact distinct left right unit ((identity_selected _ _).mpr ⟨first, held⟩)
        ((identity_selected _ _).mpr ⟨second, other⟩)
    · intro distinct left right unit held other
      obtain ⟨first, selected⟩ := (identity_selected _ _).mp held
      obtain ⟨second, chosen⟩ := (identity_selected _ _).mp other
      exact distinct left right unit first second selected chosen⟩

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

/-- The checkpoint writer writes exactly the states of a resumable profile
(`Checkpoint.save_supported`, `Checkpoint.save_refuses`). The specification names the four
discriminants of the profile and no function that the writer calls. -/
theorem checkpoint_save : Regula.ExecutableContract Checkpoint.saveBytes (fun save =>
    ∀ (construction : AgentConstruction) (state : construction.State),
      (save construction state).isOk = true ↔ Resumable construction.profile) :=
  ⟨fun construction state => by
    rw [← resumable_iff]
    cases supported : construction.profile.checkpointSupported with
    | true => simp [Checkpoint.save_supported construction state supported, Except.isOk,
        Except.toBool]
    | false => simp [Checkpoint.save_refuses construction state supported, Except.isOk,
        Except.toBool]⟩

/-- Loading refuses every byte list under a profile that is not resumable. The acceptance
of the bytes that a resumable construction saved is `checkpoint_load_accepts` in
`AcornVerif.Decisions`. The specification names the four discriminants of the profile and
no function that loading calls.

**Not claimed:** which other byte lists a resumable construction refuses. -/
theorem checkpoint_load : Regula.ExecutableContract Checkpoint.load (fun load =>
    ∀ (construction : AgentConstruction) (receiver : construction.State) (bytes : List UInt8),
      ¬Resumable construction.profile → (load construction receiver bytes).isOk = false) :=
  ⟨fun construction receiver bytes other => by
    have unsupported : construction.profile.checkpointSupported = false := by
      cases supported : construction.profile.checkpointSupported with
      | false => rfl
      | true => exact absurd ((resumable_iff _).mp supported) other
    unfold Checkpoint.load
    cases Checkpoint.loadCandidate construction bytes with
    | error refusal => rfl
    | ok image =>
      simp [bind, Except.bind, AgentConstruction.State.restore,
        Agent.restore_refuses receiver.agent image.image unsupported, Except.isOk, Except.toBool]
      rfl⟩

/-- The holding test accepts exactly an objective whose identity is the given unit
(`Assignment.holds_iff`). -/
theorem assignment_holds : Regula.ExecutableContract @Assignment.holds (fun test =>
    ∀ (config : Features.Config) (unit : Fin config.units.count)
      (assignment : Assignment config),
      @test config unit assignment = true ↔ assignment.identity = some unit) :=
  ⟨fun _ => Assignment.holds_iff⟩

/-- The identity comparison accepts exactly two objectives with the same identity
(`Assignment.same_iff`). -/
theorem assignment_same : Regula.ExecutableContract @Assignment.same (fun test =>
    ∀ (config : Features.Config) (left right : Assignment config),
      @test config left right = true ↔ left.identity = right.identity) :=
  ⟨fun _ => Assignment.same_iff⟩

/-- The retained-interest test accepts exactly a learned interest whose objective has the
identity of the target (`Interest.sameAssignment_iff`). -/
theorem interest_same : Regula.ExecutableContract @Features.Interest.sameAssignment (fun test =>
    ∀ (config : Features.Config) (interest : Features.Interest config)
      (target : Assignment config),
      @test config interest target = true ↔
        ∃ prior, interest = .learned prior ∧ prior.identity = target.identity) :=
  ⟨fun _ => Features.Interest.sameAssignment_iff⟩

/-- The utility comparison accepts exactly a unit whose stored utility key is strictly below
the other's (`Lifecycle.lessUseful_iff`). -/
theorem less_useful : Regula.ExecutableContract @Features.Lifecycle.lessUseful (fun test =>
    ∀ {shape actions config criterion dimension discounts}
      (state : Features.Lifecycle shape actions config criterion dimension discounts)
      (unit other : Fin config.units.count),
      test state unit other = true ↔
        state.progress.units[unit.val].utility.value.key <
          state.progress.units[other.val].utility.value.key) :=
  ⟨Features.Lifecycle.lessUseful_iff⟩

/-- The consistency test accepts exactly a behaviour whose reported masses are the frozen
policy's (`PolicySnapshot.consistent_iff`). -/
theorem snapshot_consistent : Regula.ExecutableContract @PolicySnapshot.consistent (fun test =>
    ∀ {count} (snapshot : PolicySnapshot count) (behaviour : Vector Binary32 count.word.toNat),
      test snapshot behaviour = true ↔ snapshot.probabilities = behaviour) :=
  ⟨PolicySnapshot.consistent_iff⟩

/-- Identity-or-refusal restoration accepts the words of every assignment under the receiving
slot function and returns that assignment (`Assignment.wordsUsing_roundtrip`).

**Not claimed:** that every accepted image is the word image of an assignment. -/
theorem assignment_admit_using : Regula.ExecutableContract Assignment.admitUsing (fun admit =>
    ∀ (dimension : Dimension) (config : Features.Config)
      (slot : Fin config.units.count → FeatIdx dimension) (assignment : Assignment config),
      admit dimension config slot (Assignment.wordsUsing slot assignment) = some assignment) :=
  ⟨fun dimension _ => Assignment.wordsUsing_roundtrip dimension⟩

/-- The raw controller step accepts exactly an action index inside the action space
(`Controller.stepRaw_refuses` is the refusal direction). -/
theorem controller_step_raw : Regula.ExecutableContract @Controller.stepRaw (fun step =>
    ∀ {config dimension actions} (controller : Controller config dimension actions)
      (features : SwiftTd.ActiveSet dimension) (raw : Nat) (reward : Binary32),
      (step controller features raw reward).isSome = true ↔ raw < actions) :=
  ⟨fun {_ _ actions} controller features raw reward => by
    unfold Controller.stepRaw Action.admit
    by_cases inside : raw < actions <;> simp [inside]⟩

/-- Agent restoration accepts an image exactly under a resumable profile
(`Agent.restore_refuses`, `Agent.restore_components`). The specification names the four
discriminants of the profile and no function that restoration calls. -/
theorem agent_restore : Regula.ExecutableContract @Agent.restore (fun restore =>
    ∀ {interface profile config criterion dimension planning}
      (state : Agent interface profile config criterion dimension planning)
      (image : AgentImage interface config criterion dimension),
      (restore state image).isSome = true ↔ Resumable profile) :=
  ⟨fun {_ profile _ _ _ _} state image => by
    rw [← resumable_iff]
    cases supported : profile.checkpointSupported <;> simp [Agent.restore, supported]⟩

/-- Profile admission refuses every feature image under a profile that is not resumable
(`FeatureProfile.unsupported_refuses`). The acceptance of the feature words of an agent image
under a resumable profile is `profile_admit_accepts` in `AcornVerif.Decisions`. The
specification names the four discriminants of the profile. -/
theorem profile_admit : Regula.ExecutableContract @FeatureProfile.admit (fun admit =>
    (∀ (profile : FeatureProfile) {actions : Word.Count} (config : Features.Config)
      (criterion : Criterion) (dimension : Dimension) {discounts : List Discount}
      (raw : RawFeatureImage actions dimension discounts),
      ¬Resumable profile → admit profile config criterion dimension raw = none)) :=
  ⟨(fun profile _ config criterion dimension _ raw other =>
    FeatureProfile.unsupported_refuses profile config criterion dimension raw (by
      cases supported : profile.checkpointSupported with
      | false => rfl
      | true => exact absurd ((resumable_iff _).mp supported) other))⟩

/-- The raw prediction-control step accepts exactly an action index inside the primitive
actions (`PredictionControl.raw_refusal` is the refusal direction). -/
theorem prediction_advance_raw :
    Regula.ExecutableContract @PredictionControl.advanceRaw (fun advance =>
    ∀ {profile criterion dimension}
        (state : PredictionControl Grid.interface profile criterion dimension)
        {config : Features.Config} (bank : Bank Host.patchShape config) (obs : Host.Observation)
        (reward : Binary32) (raw : Nat) (own : Bool),
        (advance state bank obs reward raw own).isSome = true ↔
          raw < Acorn.FeatureConstants.primitiveCount) :=
  ⟨fun state _ bank obs reward raw own => by
    show ((Action.admit Acorn.FeatureConstants.primitiveCount raw).map _).isSome = true ↔ _
    cases admitted : Action.admit Acorn.FeatureConstants.primitiveCount raw with
    | none =>
      have outside := (Action.admit_none _ _).mp admitted
      exact ⟨fun present => absurd present Bool.false_ne_true,
        fun inside => absurd inside (Nat.not_lt.mpr outside)⟩
    | some action =>
      have inside : ¬Acorn.FeatureConstants.primitiveCount ≤ raw := fun outside =>
        absurd ((Action.admit_none _ _).mpr outside) (by simp [admitted])
      exact ⟨fun _ => Nat.lt_of_not_le inside, fun _ => rfl⟩⟩

/-- The clock-predicate evaluator, on the agreement-order and snapshot-order programs with
equal leading clocks, accepts only the values the theorems state
(`ClockProgram.agreementFollows_same`, `snapshotFollows_same`), and it accepts the
snapshot-order program whenever the same process and run are not terminal, share a cycle
and resolved more attempts (`ClockProgram.snapshotFollows_goal`). The predicate's type
depends on its arity, so the statement is a requirement with no kind.

**Not claimed:** the verdict on other programs. -/
theorem predicate_eval : Regula.ExecutableContract @ClockProgram.Predicate.eval (fun eval =>
    (∀ values : Fin 6 → Nat, values 0 = values 3 →
      eval values ClockProgram.agreementFollows = true →
        values 5 = 0 ∧ (values 4 < values 1 ∨ (values 1 = values 4 ∧ values 2 = 1))) ∧
      (∀ values : Fin 14 → Nat, values 0 = values 7 →
        eval values ClockProgram.snapshotFollows = true →
          values 9 = 0 ∧ values 8 ≤ values 1) ∧
      ∀ values : Fin 14 → Nat, values 0 = values 7 → values 1 = values 8 → values 9 = 0 →
        values 3 = values 10 → values 11 < values 4 →
          eval values ClockProgram.snapshotFollows = true) :=
  ⟨⟨ClockProgram.agreementFollows_same, ClockProgram.snapshotFollows_same,
    ClockProgram.snapshotFollows_goal⟩⟩

/-- A weight enters the ranking exactly when its signed word is positive, and an entering
weight carries the bits of its own stored word as its key (`candidateOfWeight_key`). -/
theorem candidate_of_weight : Regula.ExecutableContract @candidateOfWeight (fun admit =>
    ∀ (dimension : Dimension) (config : Features.Config)
      (weights : WeightArray (.discounted .g99) dimension) (unit : Fin config.units.count),
      ((@admit dimension config weights unit).isSome = true ↔
        0 < (weights.get (unitFeature dimension config unit)).value.key) ∧
        ∀ candidate : Candidate config, @admit dimension config weights unit = some candidate →
          candidate.key =
            (weights.get (unitFeature dimension config candidate.unit)).value.bits.toNat) :=
  ⟨fun dimension config weights unit =>
    ⟨@dite_isSome _ _ (Binary32.positiveDecidable _) _,
      candidateOfWeight_key dimension config weights unit⟩⟩

/-- A unit can be replaced: it is older than the maturity threshold and, away from a free
boundary, it is the objective of no skill. Stated on the stored birth step, the clock and the
objectives, with no eligibility test. -/
def Replaceable {shape : PatchShape} {actions : Word.Count} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {discounts : List Discount}
    (state : Features.Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (unit : Fin config.units.count) : Prop :=
  state.progress.units[unit.val].birth.toNat + config.tester.maturity <
      state.progress.clock.toNat ∧
    (free = true ∨ ∀ skill ∈ state.consumers.skills.toList,
      ∀ bonus, skill.interest.held ≠ .selected unit bonus)

private theorem eligible_iff {shape : PatchShape} {actions : Word.Count}
    {config : Features.Config} {criterion : Criterion} {dimension : Dimension}
    {discounts : List Discount}
    (state : Features.Lifecycle shape actions config criterion dimension discounts)
    (free : Bool) (unit : Fin config.units.count) :
    state.eligible free unit = true ↔ Replaceable state free unit := by
  have held : ∀ assignment : Assignment config,
      ¬assignment.holds unit = true ↔ ∀ bonus, assignment ≠ .selected unit bonus := by
    intro assignment
    cases assignment with
    | neutral => simp [Assignment.holds]
    | selected other bonus =>
      simp only [Assignment.holds, beq_iff_eq, ne_eq, Assignment.selected.injEq, not_and]
      constructor
      · intro differs _ same
        exact absurd same differs
      · intro differs same
        exact differs bonus same rfl
  simp only [Features.Lifecycle.eligible, Features.Lifecycle.mature, Ensemble.holds,
    Replaceable, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    List.any_eq_false, held]

/-- Candidate selection returns no unit exactly when no unit can be replaced, and a returned
unit can be replaced and has the least stored utility among the units that can
(`Lifecycle.candidate_none_iff`, `candidate_eligible`, `candidate_least`). The specification
`Replaceable` is stated on stored data and names no eligibility test. -/
theorem lifecycle_candidate :
    Regula.ExecutableContract @Features.Lifecycle.candidate (fun candidate =>
    ∀ {shape actions config criterion dimension discounts}
        (state : Features.Lifecycle shape actions config criterion dimension discounts)
        (free : Bool),
        (candidate state free = none ↔ ∀ unit, ¬Replaceable state free unit) ∧
          ∀ unit, candidate state free = some unit → Replaceable state free unit ∧
            ∀ other, Replaceable state free other →
              state.progress.units[unit.val].utility.value.key ≤
                state.progress.units[other.val].utility.value.key) :=
  ⟨fun state free =>
    ⟨by
      rw [Features.Lifecycle.candidate_none_iff, Features.Lifecycle.eligibleCount,
        List.countP_eq_zero]
      constructor
      · intro none unit replaceable
        exact none unit (List.mem_finRange unit) ((eligible_iff state free unit).mpr replaceable)
      · intro none unit _ eligible
        exact none unit ((eligible_iff state free unit).mp eligible),
    fun unit selected =>
      ⟨(eligible_iff state free unit).mp (state.candidate_eligible free unit selected),
        fun other replaceable =>
          state.candidate_least free unit selected other
            ((eligible_iff state free other).mpr replaceable)⟩⟩⟩

/-- A total supplies a score exactly when it holds at least one sample under a nonzero
envelope: the product of its count and the squared envelope is positive. -/
theorem total_ratio : Regula.ExecutableContract @Agreement.Total.ratio (fun ratio =>
    ∀ (envelope : Nat) (total : Agreement.Total envelope),
      (@ratio envelope total).isSome = true ↔ 0 < total.count.val * envelope ^ 2) :=
  ⟨fun _ _ => dite_isSome _⟩

/-- A channel publishes a score exactly when it has no recorded fault and holds at least one
sample under a nonzero envelope (`Agreement.Channel.fault_no_score` is the fault direction). -/
theorem channel_ratio : Regula.ExecutableContract @Agreement.Channel.ratio (fun ratio =>
    ∀ (discount : Discount) (channel : Agreement.Channel discount),
      (@ratio discount channel).isSome = true ↔
        channel.fault = none ∧
          0 < channel.total.count.val * Agreement.envelopeUnits discount ^ 2) :=
  ⟨fun discount channel => by
    have present : (Agreement.Total.ratio channel.total).isSome = true ↔
        0 < channel.total.count.val * Agreement.envelopeUnits discount ^ 2 := dite_isSome _
    unfold Agreement.Channel.ratio
    cases fault : channel.fault with
    | some failure => simp
    | none => simpa using present⟩

/-- The headline score is present exactly for valid accounting over at least one goal
(`GoalAchievement.State.invalid_no_headline` is one refusal direction). -/
theorem goal_headline :
    Regula.ExecutableContract @GoalAchievement.State.headline (fun headline =>
    ∀ (goals attempts : Nat) (state : GoalAchievement.State goals attempts),
        (@headline goals attempts state).isSome = true ↔ state.invalid = false ∧ goals ≠ 0) :=
  ⟨fun goals attempts state => by
    cases invalid : state.invalid <;> by_cases empty : goals = 0 <;>
      simp [GoalAchievement.State.headline, invalid, empty]⟩

/-- An attempt is finished exactly at its step cap, or after at least one step whose carried
result reports the goal done. -/
theorem attempt_finished : Regula.ExecutableContract @Host.Attempt.finished (fun finished =>
    ∀ {config : Host.WorldConfig} {α : Type} {goal : Host.Goal} {cap : UInt64}
      (attempt : Host.Attempt config α goal cap),
      finished attempt = true ↔ attempt.steps.val = cap.toNat ∨
        (attempt.steps.val ≠ 0 ∧ attempt.run.carried.events.done = true)) :=
  ⟨fun attempt => by simp [Host.Attempt.finished]⟩

/-- A boundary decision closes the campaign exactly when it is complete or stopped. -/
theorem boundary_closing :
    Regula.ExecutableContract @Host.BoundaryDecision.closing (fun closing =>
    ∀ {size : Nat} {plan : Host.CampaignPlan size} (decision : Host.BoundaryDecision plan),
        closing decision = true ↔ decision = .complete ∨ decision = .stopped) :=
  ⟨fun decision => by cases decision <;> simp [Host.BoundaryDecision.closing]⟩

/-- A checkpoint write is scheduled at a boundary exactly when the boundary is complete or
stopped, or the writer is at phase zero of its period. `WritableCheckpoint.closing_due` is the
closing direction. -/
theorem checkpoint_due_at :
    Regula.ExecutableContract @Host.WritableCheckpoint.dueAt (fun dueAt =>
    ∀ {size : Nat} {plan : Host.CampaignPlan size} (capability : Host.WritableCheckpoint)
        (decision : Host.BoundaryDecision plan),
        dueAt capability decision = true ↔
          decision = .complete ∨ decision = .stopped ∨ capability.phase.val = 0) :=
  ⟨fun capability decision => by
    cases decision <;>
      simp [Host.WritableCheckpoint.dueAt, Host.WritableCheckpoint.due,
        Host.BoundaryDecision.closing]⟩

/-! ## Decisions that are polymorphic in an element type

A kind is stated about a function between two fixed types, so none applies to a function that
takes its element type as an argument. The proved statement holds for every element type and
is registered as a requirement with no kind. -/

/-- List decoding accepts the encodings of every list under the receiving codec, followed by
any suffix, and returns the list and the suffix (`Checkpoint.list_roundtrip`).

**Not claimed:** that every accepted byte list is such an encoding. -/
theorem list_decode : Regula.ExecutableContract @Checkpoint.decodeList (fun decode =>
    ∀ (α : Type) (codec : Checkpoint.Codec α) (values : List α) (suffix : List UInt8),
      @decode α codec values.length (values.flatMap codec.encode ++ suffix) =
        some (values, suffix)) :=
  ⟨fun _ => Checkpoint.list_roundtrip⟩

/-- Accumulating list decoding accepts the same encodings and returns the list after the
accumulator (`Checkpoint.list_into_roundtrip`).

**Not claimed:** that every accepted byte list is such an encoding. -/
theorem list_decode_into : Regula.ExecutableContract @Checkpoint.decodeListInto (fun decode =>
    ∀ (α : Type) (codec : Checkpoint.Codec α) (values : List α) (suffix : List UInt8)
      (reversed : List α),
      @decode α codec values.length (values.flatMap codec.encode ++ suffix) reversed =
        some (reversed.reverse ++ values, suffix)) :=
  ⟨fun _ => Checkpoint.list_into_roundtrip⟩

/-- A subscriber buffer accepts a value exactly when it holds fewer values than its capacity
(`Buffer.offer_iff`). -/
theorem buffer_offer : Regula.ExecutableContract @Buffer.offer (fun offer =>
    ∀ (α : Type) (capacity : Nat) (buffer : Buffer α capacity) (value : α),
      (@offer α capacity buffer value).isSome = true ↔ buffer.values.length < capacity) :=
  ⟨fun _ _ => Buffer.offer_iff⟩

/-- The schema test accepts only a table whose every entry names a schema key with a fitting
shape (`schemaCovers_sound`), and it accepts the empty table against every schema.

**Not claimed:** completeness for a nonempty table. The test reads the table in schema order
and refuses a fitting table that is listed in another order. -/
theorem schema_covers : Regula.ExecutableContract @schemaCovers (fun covers =>
    ∀ (α : Type) (fits : String → α → TelemetryShape → Bool) (table : List (String × α))
      (schema : List (String × TelemetryShape)),
      (@covers α fits table schema = true →
        ∀ entry ∈ table, ∃ shape,
          (entry.1, shape) ∈ schema ∧ fits entry.1 entry.2 shape = true) ∧
        @covers α fits [] schema = true) :=
  ⟨fun _ fits table schema => ⟨schemaCovers_sound fits table schema, rfl⟩⟩

/-! ## Definitions that a registered decision reads

A registered decision reaches each definition below, and a theorem names it. The statement
about each is exact on stored data, or it is the theorem about it. -/

/-- The identity of an objective is absent for the neutral objective and is the unit of a
selected one. The objective's type depends on the bank configuration, so the statement is a
requirement with no kind. -/
theorem assignment_identity : Regula.ExecutableContract @Assignment.identity (fun identity =>
    ∀ (config : Features.Config),
      @identity config .neutral = none ∧
        ∀ (unit : Fin config.units.count) (bonus : Bonus),
          @identity config (.selected unit bonus) = some unit) :=
  ⟨fun _ => ⟨rfl, fun _ _ => rfl⟩⟩

/-- A total admits one more sample exactly while its count is below the count limit, and an
admitted write adds one to the count and the sample to the sum (`Agreement.Total.observe_exact`).
The total's type depends on the envelope, so the statement is a requirement with no kind. -/
theorem total_observe : Regula.ExecutableContract @Agreement.Total.observe (fun observe =>
    ∀ (envelope : Nat) (total : Agreement.Total envelope) (sample : Fin (envelope ^ 2 + 1)),
      ((@observe envelope total sample).isSome = true ↔
        total.count.val < Agreement.countLimit) ∧
        ∀ next : Agreement.Total envelope, @observe envelope total sample = some next →
          next.count.val = total.count.val + 1 ∧ next.sum = total.sum + sample.val) :=
  ⟨fun envelope total sample =>
      ⟨by
        unfold Agreement.Total.observe
        rw [dite_isSome]
        exact Nat.add_lt_add_iff_right,
      fun next written => Agreement.Total.observe_exact total next sample written⟩⟩

/-- The direction table gives a direction exactly for the four movement actions. -/
theorem action_direction : Regula.ExecutableContract Host.Action.direction
    (Regula.Decides (·.isSome = true) (fun action : Host.Action =>
      action = .north ∨ action = .south ∨ action = .east ∨ action = .west)) :=
  ⟨decides (fun action => by cases action <;> simp [Host.Action.direction])
    ⟨.north, .inl rfl⟩ ⟨.wait, by simp⟩⟩

attribute [regula_decision] Host.Action.direction

/-- A successful world step advances the clock by one (`Host.World.step_clock`). The world's
type depends on the configuration, so the statement is a requirement with no kind.

**Not claimed:** which steps succeed, or the successor state. The theorems of
`AcornVerif.CurrentStep` state the successor. -/
theorem world_step : Regula.ExecutableContract @Host.World.step (fun step =>
    ∀ (config : Host.WorldConfig) (world next : Host.World config) (action : Host.Action)
      (events : Host.StepResult), @step config world action = .ok (next, events) →
        next.time = world.time + 1) :=
  ⟨fun _ => Host.World.step_clock⟩

/-- A unit is mature exactly when its birth step plus the maturity threshold is before the
clock. -/
theorem lifecycle_mature : Regula.ExecutableContract @Features.Lifecycle.mature (fun mature =>
    ∀ {shape actions config criterion dimension discounts}
      (state : Features.Lifecycle shape actions config criterion dimension discounts)
      (unit : Fin config.units.count),
      mature state unit = true ↔
        state.progress.units[unit.val].birth.toNat + config.tester.maturity <
          state.progress.clock.toNat) :=
  ⟨fun _ _ => decide_eq_true_iff⟩

/-- A unit is eligible exactly when it can be replaced: `Replaceable`, on the stored birth
step, the clock and the objectives. -/
theorem lifecycle_eligible :
    Regula.ExecutableContract @Features.Lifecycle.eligible (fun eligible =>
    ∀ {shape actions config criterion dimension discounts}
        (state : Features.Lifecycle shape actions config criterion dimension discounts)
        (free : Bool) (unit : Fin config.units.count),
        eligible state free unit = true ↔ Replaceable state free unit) :=
  ⟨eligible_iff⟩

/-- An objective holds a unit exactly when it is a selected objective of that unit. -/
private theorem holds_selected {config : Features.Config} (unit : Fin config.units.count)
    (assignment : Assignment config) :
    assignment.holds unit = true ↔ ∃ bonus, assignment = .selected unit bonus := by
  cases assignment with
  | neutral => simp [Assignment.holds]
  | selected other bonus =>
    simp only [Assignment.holds, beq_iff_eq, Assignment.selected.injEq]
    exact ⟨fun same => ⟨bonus, same, rfl⟩, fun ⟨_, same, _⟩ => same⟩

/-- A unit is held exactly when the objective of some skill is a selected objective of that
unit. -/
theorem ensemble_holds : Regula.ExecutableContract @Ensemble.holds (fun holds =>
    ∀ {actions config criterion dimension discounts}
      (ensemble : Ensemble actions config criterion dimension discounts)
      (unit : Fin config.units.count),
      holds ensemble unit = true ↔
        ∃ skill ∈ ensemble.skills.toList, ∃ bonus,
          skill.interest.held = .selected unit bonus) :=
  ⟨fun ensemble unit => by
    simp only [Ensemble.holds, List.any_eq_true, holds_selected]⟩

/-- One preference step keeps its choice for a unit that cannot be replaced. For a unit that
can, it selects that unit when there is no choice, and with a choice it selects the unit
exactly when the stored utility key of the unit is below the key of the choice
(`Lifecycle.lessUseful_iff`). -/
theorem lifecycle_prefer : Regula.ExecutableContract @Features.Lifecycle.prefer (fun prefer =>
    ∀ {shape actions config criterion dimension discounts}
      (state : Features.Lifecycle shape actions config criterion dimension discounts)
      (free : Bool) (best : Option (Fin config.units.count)) (unit : Fin config.units.count),
      (¬Replaceable state free unit → prefer state free best unit = best) ∧
        (Replaceable state free unit →
          prefer state free none unit = some unit ∧
            ∀ prior, prefer state free (some prior) unit =
              if state.progress.units[unit.val].utility.value.key <
                  state.progress.units[prior.val].utility.value.key then some unit
              else some prior)) :=
  ⟨fun state free best unit =>
    ⟨fun fixed => by
        have refused : state.eligible free unit = false :=
          Bool.eq_false_iff.mpr fun eligible =>
            fixed ((eligible_iff state free unit).mp eligible)
        simp [Features.Lifecycle.prefer, refused],
      fun replaceable => by
        have eligible := (eligible_iff state free unit).mpr replaceable
        refine ⟨by simp [Features.Lifecycle.prefer, eligible], fun prior => ?_⟩
        by_cases less : state.lessUseful unit prior = true
        · have strict := (state.lessUseful_iff unit prior).mp less
          simp [Features.Lifecycle.prefer, eligible, less, strict]
        · have refused := Bool.eq_false_iff.mpr less
          have loose : ¬(state.progress.units[unit.val].utility.value.key <
              state.progress.units[prior.val].utility.value.key) := fun strict =>
            less ((state.lessUseful_iff unit prior).mpr strict)
          simp [Features.Lifecycle.prefer, eligible, refused, loose]⟩⟩

/-- The hashed-slot potential of an objective is set exactly for a selected objective whose
unit feature is active. `unitFeature` is the slot map, which the potential also reads. -/
theorem assignment_potential : Regula.ExecutableContract @Assignment.potential (fun potential =>
    ∀ {dimension : Dimension} {config : Features.Config} (assignment : Assignment config)
      (active : SwiftTd.ActiveSet dimension),
      potential assignment active = true ↔
        ∃ unit bonus, assignment = .selected unit bonus ∧
          unitFeature dimension config unit ∈ active.indices) :=
  ⟨fun assignment active => by
    cases assignment with
    | neutral => simp [Assignment.potential, Assignment.feature]
    | selected unit bonus =>
      simp only [Assignment.potential, Assignment.feature, decide_eq_true_eq,
        Assignment.selected.injEq]
      exact ⟨fun member => ⟨unit, bonus, ⟨rfl, rfl⟩, member⟩,
        fun ⟨_, _, ⟨same, _⟩, member⟩ => same ▸ member⟩⟩

/-- The lifetime payload of a decision is present exactly when the decision ended an option,
and it carries the slot, the age and the reason of that ending
(`TemporalControl.finish_options` states that the lifetime record reads it). -/
theorem episode_end : Regula.ExecutableContract @TemporalDecision.episodeEnd (fun episodeEnd =>
    ∀ {actions} (decision : TemporalDecision actions),
      (episodeEnd decision = none ↔ decision.ended = none) ∧
        ∀ event, decision.ended = some event →
          ∃ ending, episodeEnd decision = some ending ∧ ending.slot = event.slot ∧
            ending.duration = event.age.val.toUInt32 ∧
            (ending.reason.val = 0 ↔ event.reason = .goal) ∧
            (ending.reason.val = 1 ↔ event.reason = .duration) ∧
            (ending.reason.val = 2 ↔ event.reason = .interrupted)) :=
  ⟨fun decision =>
    ⟨by simp [TemporalDecision.episodeEnd], fun event ended => by
      simp only [TemporalDecision.episodeEnd, ended, Option.map_some]
      refine ⟨_, rfl, rfl, rfl, ?_⟩
      cases event.reason <;> simp⟩⟩

/-- The feature of an objective is absent for the neutral objective and is the unit feature of
a selected one. `unitFeature` is the slot map, which the lookup reads. The objective's type
depends on the bank configuration, so the statement is a requirement with no kind. -/
theorem assignment_feature : Regula.ExecutableContract @Assignment.feature (fun feature =>
    ∀ (dimension : Dimension) (config : Features.Config),
      @feature dimension config .neutral = none ∧
        ∀ (unit : Fin config.units.count) (bonus : Bonus),
          @feature dimension config (.selected unit bonus) =
            some (unitFeature dimension config unit)) :=
  ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩⟩

/-- The phase flag after a managed entry is set exactly: after a first-loop, terminal, install,
clear or release entry, and after a plan, retire or restore entry when it was set before. The
entry is stated by its constructor. The entry's type depends on the dimension, so the
statement is a requirement with no kind. -/
theorem next_ready : Regula.ExecutableContract @SwiftTd.nextReady (fun next =>
    ∀ {dimension : Dimension} (entry : SwiftTd.Entry dimension) (before : Bool),
      @next dimension entry before = true ↔
        (∃ delta vDelta decay, entry = .first delta vDelta decay) ∨
          (∃ target, entry = .terminal target) ∨
          (∃ weights beta, entry = .install weights beta) ∨ entry = .clear ∨
          entry = .release ∨
          (before = true ∧
            ((∃ features target, entry = .plan features target) ∨
              (∃ idx, entry = .retire idx) ∨ (∃ raw, entry = .restoreWeights raw) ∨
              ∃ raw, entry = .restoreBeta raw))) :=
  ⟨fun entry before => by cases entry <;> simp [SwiftTd.nextReady]⟩

end Acorn.Decisions
