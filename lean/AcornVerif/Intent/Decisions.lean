/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.DayCycleConsequences
import AcornVerif.Intent.HashConsequences
import AcornVerif.Intent.WorldInterfaceConsequences
import Acorn.Host.Task

/-!
# Decisions made on the owner's behalf, and Acorn's deliverables

On 2026-10-29 the owner decided how the intent-first method divides the work: the owner states
intent where they hold it, and below that level each detail of a specification is a design
decision the owner's agents make and record, with its reason tied to the owner's intent, marked as
decided on the owner's behalf and never presented as the owner's confirmation. The owner's
attention goes only to a plain restatement of their intent, to real forks the intent does not
settle that change what they get, and to one-way doors and quality-for-cost trades. The owner
likened the division to an interface and its implementation: their intent is a system's contract,
and records of internal functions such as these are the agents' own design.

This module declares Acorn's three lean-intent deliverables, `dayDeliverable`, `hashDeliverable`
and `worldInterfaceDeliverable`: each holds its record, the record's explanation, the answers it
keeps and the proof that the record keeps them. The first two are records of internal functions, the
agents' design; the third is the record of contract 1 of Acorn's mission contract, the interface
every world meets, whose plain restatement the owner confirmed on 2026-11-03. The day record Acorn
declares, `AcornVerif.Intent.DayCycle.dayCycle`, is the generic
record `dayCycleFor` at the types of Acorn's world: one situation, since Acorn's day reads nothing
of a situation but the clock (`AcornVerif.Intent.DayCycle.dayPhase_clock`), Acorn's actions, the
day-phase byte the agent sees and energy as a natural number. The hash record,
`AcornVerif.Intent.Hash.hashes`, and the interface record,
`AcornVerif.Intent.WorldInterface.worldInterface`, have no parameters.

The owners' log, `ownersLog` in `AcornVerif.Intent.OwnersLog`, holds every statement as the text
lean-intent's `Statement.print` writes, which `LeanIntent.Confirmation.Read.check` reads from the
build. It declares the owner, the
owner's delegation of the decisions below their intent to the agents (`agents-below-intent`), and
each decision as an answer the agents gave under it, so the log itself says the owner did not give
it. The answers of 2026-10-29 named the record's revision by a commit and its predicates in a short
form; the confirmation check compares an answer's revision and predicate with the texts it computes
from the build (`LeanIntent.Render.revisionText`, `LeanIntent.Render.consequenceText`), so on
2026-11-03 the agents retracted each of them and gave each again, with the same verdict, against
those texts, as `LeanIntent.Confirmation.Read.answerStatement` writes them. They also answered, for
the day and hash records, the question every revision asks, whether its rendering restates the
intent: those records are the agents' design, so that answer is the agents', and each of their
explanations records its restatement as unconfirmed by the owner. Each decision's reason is in the
pilot report, `docs/spec-first-pilot.md`, which the answers' source names
(`AcornVerif.Intent.reasons`).

An answer's texts change whenever the rendering of its record or of a definition its predicate
reaches changes, and the check then refuses it, naming it, until it is retracted and given again
against the new texts by someone the delegation lets answer.

The interface record is settled differently. Its explanation records its restatement as confirmed by
the owner, whose answer of 2026-11-03 the log holds, and each consequence it shows as derived from
that confirmation, so its deliverable keeps no answer; the consequences decided on the owner's
behalf are recorded with their reasons in the record's confirmation file,
`lean/AcornVerif/Intent/WorldInterface.md`.

Two decisions are recorded in prose only, because they are no consequence of a record: the day
record counts time in whole ticks with one clock for the whole world (its shape), and the hash
record no longer asks that the two functions never systematically share their spots (it leaves
that unsaid, since in Acorn the two never share a space of spots). One decision is the owner's
own: the hash record bounds no collision rate, which the owner accepted as not covered.
-/

namespace AcornVerif.Intent.DayCycle

open LeanIntent

/-- The day record at the types of Acorn's world: one situation, Acorn's actions, the day-phase
byte the agent sees, and energy as a natural number. This is the record Acorn declares as its
deliverable and whose answers the owners' log holds. -/
def dayCycle : IntentRecord (DayWorld Unit Acorn.Host.Action UInt8 Nat) :=
  dayCycleFor Unit Acorn.Host.Action UInt8 Nat

/-- The sights of the four quarters that the day record's consequences use: the quarter's index,
as a byte. -/
def quarterSight (i : Fin 4) : UInt8 := i.val.toUInt8

theorem quarterSight_injective : ∀ i j, quarterSight i = quarterSight j → i = j := by decide

/-- The day record explained at the types of Acorn's world, with the witnesses its consequences
need: the one situation, waiting, the energy amounts 0, 1 and 2, and the quarters' sights. -/
def dayExplained : Explanation dayCycle :=
  dayCycleExplained () .wait (lo := 0) (hi := 1) (hi' := 2) (by decide) (by decide) (by decide)
    quarterSight_injective

end AcornVerif.Intent.DayCycle

namespace AcornVerif.Intent.Decisions

open LeanIntent AcornVerif.Intent.DayCycle AcornVerif.Intent.Hash

/-! ## The typed answers, kept by each record's current revision -/

section

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
    (o₁ o₂ : Obs) : Keeps (dayCycleFor Ctx Act Obs E) (dayAnswers lo hi o₁ o₂) := by
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

end

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

/-- Each answer, given by the agents under the owner's delegation. -/
def byAgents {W : Type} (answers : List (Answer W)) : List (Attributed W) :=
  answers.map fun answer => ⟨answer, agentsAnswer⟩

theorem byAgents_answers {W : Type} (answers : List (Answer W)) :
    (byAgents answers).map (·.answer) = answers := by
  simp only [byAgents, List.map_map]
  exact List.map_id _

/-! ## The deliverables -/

/-- The day record's deliverable: the record at the types of Acorn's world, its explanation, and
the decisions on its consequences, the one the record now refutes, that the agent may see only day
or night (at the sights 0 by day and 4 by night), among them. -/
def dayDeliverable : Deliverable (DayWorld Unit Acorn.Host.Action UInt8 Nat) where
  record := dayCycle
  explanation := dayExplained
  answers := byAgents (dayAnswers (lo := 0) (hi := 1) 0 4)
  keeps := by
    rw [byAgents_answers]
    exact dayCycle_keeps (Obs := UInt8) () Acorn.Host.Action.wait (lo := 0) (hi := 1) (hi' := 2)
      (by decide) (by decide) (by decide) quarterSight_injective 0 4

/-- The hash record's deliverable: the record, its explanation and the decisions on its
consequences. No implementation is declared for it, since no theorem proves that Acorn's
`Rng.hash2` and `Rng.hash3` fulfil it (rbeauchamp/acorn#184). -/
def hashDeliverable : Deliverable Hashes where
  record := hashes
  explanation := hashesExplained
  answers := byAgents hashAnswers
  keeps := by
    rw [byAgents_answers]
    exact hashes_keeps

/-- The interface record's deliverable: the record of contract 1, its explanation, and no kept
answer, since its restatement stands as the owner's and every consequence it shows is derived from
it. No implementation is declared for it until the executing code is proved against it
(rbeauchamp/acorn#213). -/
def worldInterfaceDeliverable : Deliverable WorldInterface.System where
  record := WorldInterface.worldInterface
  explanation := WorldInterface.worldInterfaceExplained
  answers := []
  keeps := (keeps_iff _ _).mpr fun _ h => nomatch h

end AcornVerif.Intent.Decisions
