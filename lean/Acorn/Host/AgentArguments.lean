/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Digits
import Acorn.Host.AgentAdmission

/-!
# Shared native full-agent arguments

All current profile, criterion, planning, dimension and representation words
are admitted before learner allocation. Native agent and checkpoint commands
share this parser and the same raw-observation adapter. Both commands run the prefix
fold of `Agent.act`, which is the default step order, so every construction they admit
declares that order and they take no order word. Each number is read by `Digits.natural`, the
reader of every Acorn command line: an optional plus sign, then the digits `0` to `9`.
-/
namespace Acorn.Host.AgentArguments
open Features Handcrafted

/-- Full native profile parsing includes every library discriminator, not just CLI research presets. -/
def profile (mode credit rate subtasks : String) : Option FeatureProfile := do
  let mode ← match mode with
    | "final" => some EvaluationMode.final | "frozen" => some .frozen
    | "without-reach" => some .withoutReachRelation | "primitive" => some .primitiveOnly | _ => none
  let credit ← match credit with
    | "per-step" => some ControlCredit.perStep | "catch-up" => some .smdpCatchUp
    | "no-span" => some .noSpanCredit | _ => none
  let rate ← match rate with
    | "declared" => some RatePolicy.declared | "own" => some .perLearner
    | "shared" => some .shared | "annealed" => some .annealed | _ => none
  let subtasks ← match subtasks with
    | "learned" => some SubtaskPolicy.learned | "spatial" => some .spatial | _ => none
  return ⟨mode, credit, rate, subtasks⟩

/-- Raw-word diagnostics provide observations, never a second policy or evaluator. -/
def input (construction : AgentConstruction) (word : UInt64) :
    AgentInput construction.config construction.criterion construction.dimension :=
  .act (⟨Vector.replicate _ (Vector.replicate _ ⟨word.toUInt8, 0, 0⟩),
      word.toUInt8, 0, .none, ⟨0, 0, 0, 0, false, false⟩⟩)
    { reward := ⟨word.toUInt32⟩, events := { done := word &&& 1 == 1 } }

/-- An unsigned number of the command line (`Digits.natural`), refused at `2 ^ 64` or more
before it narrows to a machine word. -/
def word (text : String) : Option UInt64 := do
  let value ← Digits.natural text
  if value < 2^64 then some value.toUInt64 else none

/-- One admitted receiver context and its optional raw diagnostic input words. The
context is a construction of the default step order: the native drivers fold
`Agent.act`, the step of that order, and take no order word. -/
def admit (arguments : List String) : Option (DefaultConstruction × List UInt64) := do
  match arguments with
  | seed :: exponent :: tilings :: units :: mode :: credit :: rate :: subtasks :: criterion :: planning :: words =>
    let profile ← profile mode credit rate subtasks
    let criterion ← match criterion with
      | "discounted" => some Criterion.discounted | "differential" => some .differential | _ => none
    let planning ← PlanningSelection.parse planning
    let seed ← word seed
    let tilings ← word tilings
    let units ← Digits.natural units
    let exponent ← Digits.natural exponent
    match admitted : AgentConstruction.admit profile criterion planning .learnThenAct seed
        tilings units exponent with
    | none => none
    | some construction =>
      let words ← words.mapM word
      return (⟨construction, AgentConstruction.admit_order profile criterion planning
        .learnThenAct seed tilings units exponent construction admitted⟩, words)
  | _ => none

/-! ## The grammar of the arguments

The relations below state the argument lists that `admit` accepts and what it returns for
them, with no executed function: `agent_arguments_admit` in `Acorn.Decisions` proves that
`admit` accepts exactly the lists of `Admitted`, and `agent_arguments_admit_value` that it
returns a construction and input words exactly when the list spells them field by field
(`Constructs`). -/

/-- The word of an evaluation mode. -/
def ModeSpelled (text : String) (mode : EvaluationMode) : Prop :=
  (text = "final" ∧ mode = .final) ∨ (text = "frozen" ∧ mode = .frozen) ∨
    (text = "without-reach" ∧ mode = .withoutReachRelation) ∨
    (text = "primitive" ∧ mode = .primitiveOnly)

/-- The word of a primitive-credit choice. -/
def CreditSpelled (text : String) (credit : ControlCredit) : Prop :=
  (text = "per-step" ∧ credit = .perStep) ∨ (text = "catch-up" ∧ credit = .smdpCatchUp) ∨
    (text = "no-span" ∧ credit = .noSpanCredit)

/-- The word of a rate source. -/
def RateSpelled (text : String) (rate : RatePolicy) : Prop :=
  (text = "declared" ∧ rate = .declared) ∨ (text = "own" ∧ rate = .perLearner) ∨
    (text = "shared" ∧ rate = .shared) ∨ (text = "annealed" ∧ rate = .annealed)

/-- The word of a subtask source. -/
def SubtasksSpelled (text : String) (subtasks : SubtaskPolicy) : Prop :=
  (text = "learned" ∧ subtasks = .learned) ∨ (text = "spatial" ∧ subtasks = .spatial)

/-- The word of a control criterion. -/
def CriterionSpelled (text : String) (criterion : Criterion) : Prop :=
  (text = "discounted" ∧ criterion = .discounted) ∨
    (text = "differential" ∧ criterion = .differential)

/-- The four words of a feature profile, in the order mode, credit, rate and subtasks. -/
def ProfileSpelled (mode credit rate subtasks : String) (profile : FeatureProfile) : Prop :=
  ModeSpelled mode profile.mode ∧ CreditSpelled credit profile.credit ∧
    RateSpelled rate profile.rate ∧ SubtasksSpelled subtasks profile.subtasks

/-- The argument lists of the native drivers, stated with no executed function: a seed, a
capacity exponent, a tiling word and a bank size, the four words of a profile, the word of a
criterion and the word of a planning selection, then raw input words. Each number is the text
of an unsigned number of the command line (`Digits.Natural`). The seed, the tiling word and
each input word are below `2 ^ 64`; the tiling word is positive, the bank size is from 1 to
65535 and the exponent is below 32, which are the conditions of `AgentConstruction.admit`
(`AgentConstruction.admit_iff`). -/
def Admitted (arguments : List String) : Prop :=
  ∃ (seed exponent tilings units mode credit rate subtasks criterion planning : String)
    (words : List String),
    arguments = [seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion,
      planning] ++ words ∧
    (∃ profile, ProfileSpelled mode credit rate subtasks profile) ∧
    (∃ selected, CriterionSpelled criterion selected) ∧
    (∃ selection, planning = PlanningSelection.name selection) ∧
    (∃ n, Digits.Natural seed n ∧ n < 2 ^ 64) ∧
    (∃ n, Digits.Natural tilings n ∧ 0 < n ∧ n < 2 ^ 64) ∧
    (∃ n, Digits.Natural units n ∧ 0 < n ∧ n ≤ 65535) ∧
    (∃ n, Digits.Natural exponent n ∧ n < 32) ∧
    ∀ word ∈ words, ∃ n, Digits.Natural word n ∧ n < 2 ^ 64

/-- The construction and raw input words that an argument list spells, field by field, with no
executed function: the list is ten words and the input words; the construction's profile is
the one its four profile words spell, its criterion and planning selection are the ones their
words spell, and its step order is the default one; its seed and tiling word are the values of
their numerals, its bank holds the value of the bank-size numeral in units and its tester is
the declared one; its capacity is two to the power of the value of the exponent numeral; and
the input words are the values of their numerals, in order. -/
def Constructs (arguments : List String) (construction : AgentConstruction)
    (words : List UInt64) : Prop :=
  ∃ (seed exponent tilings units mode credit rate subtasks criterion planning : String)
    (texts : List String) (e : Nat),
    arguments = [seed, exponent, tilings, units, mode, credit, rate, subtasks, criterion,
      planning] ++ texts ∧
    ProfileSpelled mode credit rate subtasks construction.profile ∧
    CriterionSpelled criterion construction.criterion ∧
    planning = PlanningSelection.name construction.planning ∧
    construction.order = .learnThenAct ∧ Digits.Natural seed construction.config.seed.toNat ∧
    Digits.Natural tilings construction.config.tilings.toNat ∧
    Digits.Natural units construction.config.units.count ∧ Digits.Natural exponent e ∧
    construction.dimension.capacity = 2 ^ e ∧ construction.config.tester = declaredTester ∧
    words.length = texts.length ∧ ∀ pair ∈ texts.zip words, Digits.Natural pair.1 pair.2.toNat

end Acorn.Host.AgentArguments
