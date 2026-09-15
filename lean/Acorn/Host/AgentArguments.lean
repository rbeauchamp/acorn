/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentAdmission

/-!
# Shared native full-agent arguments

All current profile, criterion, planning, dimension and representation words
are admitted before learner allocation. Native agent and checkpoint commands
share this parser and the same raw-observation adapter.
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
    | "own" => some RatePolicy.perLearner | "shared" => some .shared
    | "annealed" => some .annealed | _ => none
  let subtasks ← match subtasks with
    | "learned" => some SubtaskPolicy.learned | "spatial" => some .spatial | _ => none
  return ⟨mode, credit, rate, subtasks⟩

/-- Raw-word diagnostics provide observations, never a second policy or evaluator. -/
def input (construction : AgentConstruction) (word : UInt64) :
    AgentInput construction.config construction.criterion construction.dimension :=
  .act (⟨Vector.replicate _ (Vector.replicate _ ⟨word.toUInt8, 0, 0⟩),
      word.toUInt8, 0, .none, ⟨0, 0, 0, 0, false, false⟩⟩)
    { reward := ⟨word.toUInt32⟩, events := { done := word &&& 1 == 1 } }

/-- Unsigned admission refuses overflow before narrowing to a machine word. -/
def word (text : String) : Option UInt64 := do
  let value ← text.toNat?
  if value < 2^64 then some value.toUInt64 else none

/-- One admitted receiver context and its optional raw diagnostic input words. -/
def admit (arguments : List String) : Option (AgentConstruction × List UInt64) := do
  match arguments with
  | seed :: exponent :: tilings :: units :: mode :: credit :: rate :: subtasks :: criterion :: planning :: words =>
    let profile ← profile mode credit rate subtasks
    let criterion ← match criterion with
      | "discounted" => some Criterion.discounted | "differential" => some .differential | _ => none
    let planning ← match planning with
      | "none" => some PlanningSelection.none | "scalar" => some .scalar | _ => none
    let seed ← word seed
    let tilings ← word tilings
    let units ← units.toNat?
    let exponent ← exponent.toNat?
    let construction ← AgentConstruction.admit profile criterion planning seed tilings units exponent
    let words ← words.mapM word
    return (construction, words)
  | _ => none

end Acorn.Host.AgentArguments
