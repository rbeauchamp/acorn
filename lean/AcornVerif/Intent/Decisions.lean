/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.DayCycleConsequences
import AcornVerif.Intent.HashConsequences

/-!
# Decisions made on the owner's behalf

On 2026-10-29 the owner decided how the spec-first method divides the work: the owner states
intent where they hold it, and below that level each detail of a specification is a design
decision the owner's agents make and record, with its reason tied to the owner's intent, marked as
decided on the owner's behalf and never presented as the owner's confirmation. The owner's
attention goes only to a plain restatement of their intent, to real forks the intent does not
settle that change what they get, and to one-way doors and quality-for-cost trades. The owner
likened the division to an interface and its implementation: their intent is a system's contract,
and records of internal functions such as these are the agents' own design.

This module records the decisions for the day record (`AcornVerif.Intent.DayCycle.dayCycle`) and
the hash record (`AcornVerif.Intent.Hash.hashes`) twice. As statements of lean-intent's owners'
log (`ownersLog`), each decision is an answer by the principal `agents` under the owner's
delegation `agents-below-intent`, so the log itself says the owner did not give it. As typed
answers (`dayAnswers`, `hashAnswers`), each is kept by the current revision of its record
(`dayAccepted`, `hashAccepted`), so a revision that broke one would fail to build. Each decision's
reason is in the pilot report, `docs/spec-first-pilot.md`, which the answers' sources cite.

Two decisions are recorded in prose only, because they are no consequence of a record: the day
record counts time in whole ticks with one clock for the whole world (its shape), and the hash
record no longer asks that the two functions never systematically share their spots (it leaves
that unsaid, since in Acorn the two never share a space of spots). One decision is the owner's
own: the hash record bounds no collision rate, which the owner accepted as not covered.
-/

namespace AcornVerif.Intent.Decisions

open LeanIntent AcornVerif.Intent.DayCycle AcornVerif.Intent.Hash

/-! ## The typed answers, kept by each record's current revision -/

variable {Ctx Act Obs E : Type} [LT E]

/-- The decisions on the day record's consequences. Declining that the agent may see only day or
night is what made the record read "where in the day" as at least the quarter of the day. -/
def dayAnswers (lo hi : E) (o₁ o₂ : Obs) : List (Answer (DayWorld Ctx Act Obs E)) :=
  [⟨everyDayAlike, .confirmed⟩, ⟨nightAlwaysDearer, .confirmed⟩,
    ⟨tellsDayFromNightAlways, .confirmed⟩, ⟨seesQuarterOfDay, .confirmed⟩,
    ⟨longDay, .confirmed⟩, ⟨dayOrNightOnlyWorld lo hi o₁ o₂, .declined⟩,
    ⟨nightCostVaries, .confirmed⟩]

/-- The day record keeps every decision on its consequences. -/
theorem dayCycle_keeps (c : Ctx) (a : Act) {lo hi hi' : E} (hlt : lo < hi) (hlt' : lo < hi')
    (hne : hi ≠ hi') {sight : Fin 4 → Obs} (hsight : ∀ i j, sight i = sight j → i = j)
    (o₁ o₂ : Obs) : Keeps (dayCycle Ctx Act Obs E) (dayAnswers lo hi o₁ o₂) := by
  refine (keeps_iff _ _).mpr fun x hx => ?_
  simp only [dayAnswers, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact everyDayAlike_holds
  · exact nightAlwaysDearer_holds
  · exact tellsDayFromNightAlways_holds
  · exact seesQuarterOfDay_holds
  · exact longDay_holds hlt hsight
  · exact fun w hw (he : w = dayOrNightOnly lo hi o₁ o₂) =>
      dayCycle_refutes_dayOrNightOnly c lo hi o₁ o₂ (he ▸ hw)
  · exact nightCostVaries_holds c a hlt hlt' hne hsight

/-- The day record's current revision, accepted under the decisions. -/
def dayAccepted (c : Ctx) (a : Act) {lo hi hi' : E} (hlt : lo < hi) (hlt' : lo < hi')
    (hne : hi ≠ hi') {sight : Fin 4 → Obs} (hsight : ∀ i j, sight i = sight j → i = j)
    (o₁ o₂ : Obs) : Accepted (dayAnswers (Ctx := Ctx) (Act := Act) lo hi o₁ o₂) :=
  ⟨dayCycle Ctx Act Obs E, dayCycle_keeps c a hlt hlt' hne hsight o₁ o₂⟩

/-- The decisions on the hash record's consequences. -/
def hashAnswers : List (Answer Hashes) :=
  [⟨oneChangeMoves, .confirmed⟩, ⟨noFixedRule, .confirmed⟩,
    ⟨rulesOutPlainCombinations, .confirmed⟩, ⟨replay, .confirmed⟩]

/-- The hash record keeps every decision on its consequences. -/
theorem hashes_keeps : Keeps hashes hashAnswers := by
  refine (keeps_iff _ _).mpr fun x hx => ?_
  simp only [hashAnswers, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact oneChangeMoves_holds
  · exact noFixedRule_holds
  · exact rulesOutPlainCombinations_holds
  · exact replay_holds

/-- The hash record's current revision, accepted under the decisions. -/
def hashAccepted : Accepted hashAnswers := ⟨hashes, hashes_keeps⟩

/-! ## The owners' log -/

/-- Where each decision's reason is kept. -/
def reasons : String := "docs/spec-first-pilot.md, The decisions made on the owner's behalf"

/-- The owners' log of the two records: the owner, the owner's delegation of the decisions below
their intent to the agents, and each decision as an answer the agents gave under it. -/
def ownersLog : List Statement := [
  { project := .of "acorn", id := .of "owners", date := ⟨2026, 10, 29, by decide⟩
    source := .reference "https://github.com/rbeauchamp/acorn"
    body := .owners { principals := [⟨.of "owner", []⟩], threshold := none } },
  { project := .of "acorn", id := .of "agents-below-intent", date := ⟨2026, 10, 29, by decide⟩
    source := .words "Yes, apply it"
    body := .delegation
      { delegator := ⟨.of "owner", none⟩
        delegate := ⟨.of "agents", []⟩
        scope := { records := .only ["AcornVerif.Intent.DayCycle.dayCycle",
          "AcornVerif.Intent.Hash.hashes"], confirm := true, decline := true, retract := true }
        mayPassOn := false } },
  { project := .of "acorn", id := .of "day-1", date := ⟨2026, 10, 29, by decide⟩
    source := .reference reasons
    body := .answer
      { author := ⟨.of "agents", some (.of "agents-below-intent")⟩
        record := "AcornVerif.Intent.DayCycle.dayCycle"
        revision := "commit 50051c749d9b94ea577bba2bde577552337df271"
        consequence := "every day lasts the same even number of ticks, at least two, placed alike"
        kind := .entailment
        predicate := "fun w => 2 ≤ w.length ∧ w.length % 2 = 0 ∧ ∀ t, w.night (t + w.length) = w.night t"
        verdict := .confirmed } },
  { project := .of "acorn", id := .of "day-2", date := ⟨2026, 10, 29, by decide⟩
    source := .reference reasons
    body := .answer
      { author := ⟨.of "agents", some (.of "agents-below-intent")⟩
        record := "AcornVerif.Intent.DayCycle.dayCycle"
        revision := "commit 50051c749d9b94ea577bba2bde577552337df271"
        consequence := "every action costs more at any night moment than at any daytime moment"
        kind := .entailment
        predicate := "fun w => ∀ c a t t', w.night t = true → w.night t' = false → w.cost t' c a < w.cost t c a"
        verdict := .confirmed } },
  { project := .of "acorn", id := .of "day-3", date := ⟨2026, 10, 29, by decide⟩
    source := .reference reasons
    body := .answer
      { author := ⟨.of "agents", some (.of "agents-below-intent")⟩
        record := "AcornVerif.Intent.DayCycle.dayCycle"
        revision := "commit 50051c749d9b94ea577bba2bde577552337df271"
        consequence := "what the agent sees always tells day from night"
        kind := .entailment
        predicate := "fun w => ∀ t t' c c', w.sees t c = w.sees t' c' → w.night t = w.night t'"
        verdict := .confirmed } },
  { project := .of "acorn", id := .of "day-4", date := ⟨2026, 10, 29, by decide⟩
    source := .reference reasons
    body := .answer
      { author := ⟨.of "agents", some (.of "agents-below-intent")⟩
        record := "AcornVerif.Intent.DayCycle.dayCycle"
        revision := "commit 50051c749d9b94ea577bba2bde577552337df271"
        consequence := "a day may last 1000 ticks"
        kind := .possibility
        predicate := "fun w => w.length = 1000"
        verdict := .confirmed } },
  { project := .of "acorn", id := .of "day-5a", date := ⟨2026, 10, 29, by decide⟩
    source := .reference reasons
    body := .answer
      { author := ⟨.of "agents", some (.of "agents-below-intent")⟩
        record := "AcornVerif.Intent.DayCycle.dayCycle"
        revision := "commit 50051c749d9b94ea577bba2bde577552337df271"
        consequence := "what the agent sees always tells it which quarter of the day it is in"
        kind := .entailment
        predicate := "fun w => ∃ start, ∀ t t' c c', w.sees t c = w.sees t' c' → quarter w.length start t = quarter w.length start t'"
        verdict := .confirmed } },
  { project := .of "acorn", id := .of "day-5b", date := ⟨2026, 10, 29, by decide⟩
    source := .reference reasons
    body := .answer
      { author := ⟨.of "agents", some (.of "agents-below-intent")⟩
        record := "AcornVerif.Intent.DayCycle.dayCycle"
        revision := "commit 50051c749d9b94ea577bba2bde577552337df271"
        consequence := "the agent may see only whether it is day or night"
        kind := .possibility
        predicate := "fun w => w = dayOrNightOnly lo hi o₁ o₂"
        verdict := .declined } },
  { project := .of "acorn", id := .of "day-6", date := ⟨2026, 10, 29, by decide⟩
    source := .reference reasons
    body := .answer
      { author := ⟨.of "agents", some (.of "agents-below-intent")⟩
        record := "AcornVerif.Intent.DayCycle.dayCycle"
        revision := "commit 50051c749d9b94ea577bba2bde577552337df271"
        consequence := "an action may cost more at one night moment than at another"
        kind := .possibility
        predicate := "fun w => ∃ c a t t', w.night t = true ∧ w.night t' = true ∧ w.cost t c a ≠ w.cost t' c a"
        verdict := .confirmed } },
  { project := .of "acorn", id := .of "hash-1", date := ⟨2026, 10, 29, by decide⟩
    source := .reference reasons
    body := .answer
      { author := ⟨.of "agents", some (.of "agents-below-intent")⟩
        record := "AcornVerif.Intent.Hash.hashes"
        revision := "commit 50051c749d9b94ea577bba2bde577552337df271"
        consequence := "changing any one input always moves the spot"
        kind := .entailment
        predicate := "fun w => OneInputMoves w.hash2 ∧ OneInputMoves w.hash3"
        verdict := .confirmed } },
  { project := .of "acorn", id := .of "hash-2", date := ⟨2026, 10, 29, by decide⟩
    source := .reference reasons
    body := .answer
      { author := ⟨.of "agents", some (.of "agents-below-intent")⟩
        record := "AcornVerif.Intent.Hash.hashes"
        revision := "commit 50051c749d9b94ea577bba2bde577552337df271"
        consequence := "no fixed rule of reordering and shifting the inputs keeps every spot"
        kind := .entailment
        predicate := "fun w => NoRuleKeepsSpots w.hash2 ∧ NoRuleKeepsSpots w.hash3"
        verdict := .confirmed } },
  { project := .of "acorn", id := .of "hash-3", date := ⟨2026, 10, 29, by decide⟩
    source := .reference reasons
    body := .answer
      { author := ⟨.of "agents", some (.of "agents-below-intent")⟩
        record := "AcornVerif.Intent.Hash.hashes"
        revision := "commit 50051c749d9b94ea577bba2bde577552337df271"
        consequence := "neither function combines its inputs by plain exclusive or or plain addition"
        kind := .entailment
        predicate := "fun w => w.hash2 ≠ xorAll ∧ w.hash2 ≠ addAll ∧ w.hash3 ≠ xorAll ∧ w.hash3 ≠ addAll"
        verdict := .confirmed } },
  { project := .of "acorn", id := .of "hash-6", date := ⟨2026, 10, 29, by decide⟩
    source := .reference reasons
    body := .answer
      { author := ⟨.of "agents", some (.of "agents-below-intent")⟩
        record := "AcornVerif.Intent.Hash.hashes"
        revision := "commit 50051c749d9b94ea577bba2bde577552337df271"
        consequence := "the same inputs always give the same spot"
        kind := .entailment
        predicate := "fun w => ∀ x y, x = y → w.hash2 x = w.hash2 y ∧ w.hash3 x = w.hash3 y"
        verdict := .confirmed } }]

end AcornVerif.Intent.Decisions
