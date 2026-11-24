import Acorn.Digits
import Acorn.Host.AgentAdmission

namespace Acorn.Host.AgentArguments
open Features Handcrafted

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

def input (construction : AgentConstruction) (word : UInt64) :
    AgentInput construction.config construction.criterion construction.dimension :=
  .act (⟨Vector.replicate _ (Vector.replicate _ ⟨word.toUInt8, 0, 0⟩),
      word.toUInt8, 0, .none, ⟨0, 0, 0, 0, false, false⟩⟩)
    { reward := ⟨word.toUInt32⟩, events := { done := word &&& 1 == 1 } }

def word (text : String) : Option UInt64 := do
  let value ← Digits.natural text
  if value < 2^64 then some value.toUInt64 else none

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

def ModeSpelled (text : String) (mode : EvaluationMode) : Prop :=
  (text = "final" ∧ mode = .final) ∨ (text = "frozen" ∧ mode = .frozen) ∨
    (text = "without-reach" ∧ mode = .withoutReachRelation) ∨
    (text = "primitive" ∧ mode = .primitiveOnly)

def CreditSpelled (text : String) (credit : ControlCredit) : Prop :=
  (text = "per-step" ∧ credit = .perStep) ∨ (text = "catch-up" ∧ credit = .smdpCatchUp) ∨
    (text = "no-span" ∧ credit = .noSpanCredit)

def RateSpelled (text : String) (rate : RatePolicy) : Prop :=
  (text = "declared" ∧ rate = .declared) ∨ (text = "own" ∧ rate = .perLearner) ∨
    (text = "shared" ∧ rate = .shared) ∨ (text = "annealed" ∧ rate = .annealed)

def SubtasksSpelled (text : String) (subtasks : SubtaskPolicy) : Prop :=
  (text = "learned" ∧ subtasks = .learned) ∨ (text = "spatial" ∧ subtasks = .spatial)

def CriterionSpelled (text : String) (criterion : Criterion) : Prop :=
  (text = "discounted" ∧ criterion = .discounted) ∨
    (text = "differential" ∧ criterion = .differential)

def ProfileSpelled (mode credit rate subtasks : String) (profile : FeatureProfile) : Prop :=
  ModeSpelled mode profile.mode ∧ CreditSpelled credit profile.credit ∧
    RateSpelled rate profile.rate ∧ SubtasksSpelled subtasks profile.subtasks

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
