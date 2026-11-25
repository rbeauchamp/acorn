import AcornVerif.Intent.DayCycleConsequences
import AcornVerif.Intent.Delegation
import AcornVerif.Intent.HashConsequences
import AcornVerif.Intent.WorldInterfaceConsequences
import AcornVerif.Intent.OneStreamConsequences
import Acorn.Host.Task

namespace AcornVerif.Intent.DayCycle

open LeanIntent

def dayCycle : IntentRecord (DayWorld Unit Acorn.Host.Action UInt8 Nat) :=
  dayCycleFor Unit Acorn.Host.Action UInt8 Nat

def quarterSight (i : Fin 4) : UInt8 := i.val.toUInt8

theorem quarterSight_injective : ∀ i j, quarterSight i = quarterSight j → i = j := by decide

def dayExplained : Explanation dayCycle :=
  let base := dayCycleExplained () .wait (lo := 0) (hi := 1) (hi' := 2) (by decide) (by decide)
    (by decide) quarterSight_injective
  ({ base with
      consequences := base.consequences.map fun s =>
        { s with settled := .answered agentsAnswer .confirmed } } :
    Explanation (dayCycleFor Unit Acorn.Host.Action UInt8 Nat))

end AcornVerif.Intent.DayCycle

namespace AcornVerif.Intent.Decisions

open LeanIntent AcornVerif.Intent.DayCycle AcornVerif.Intent.Hash

section

variable {Ctx Act Obs E : Type} [LT E]

def dayAnswers (lo hi : E) (o₁ o₂ : Obs) : List (Answer (DayWorld Ctx Act Obs E)) :=
  [⟨everyDayAlike, .confirmed⟩, ⟨nightAlwaysDearer, .confirmed⟩,
    ⟨tellsDayFromNightAlways, .confirmed⟩, ⟨seesQuarterOfDay, .confirmed⟩,
    ⟨longDay, .confirmed⟩, ⟨dayOrNightOnlyWorld lo hi o₁ o₂, .declined⟩,
    ⟨nightCostVaries, .confirmed⟩]

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

def hashAnswers : List (Answer Hashes) :=
  [⟨oneChangeMoves, .confirmed⟩, ⟨noFixedRule, .confirmed⟩,
    ⟨rulesOutPlainCombinations, .confirmed⟩, ⟨replay, .confirmed⟩]

theorem hashes_keeps : Keeps hashes hashAnswers := by
  refine (keeps_iff _ _).mpr fun x hx => ?_
  simp only [hashAnswers, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact oneChangeMoves_holds
  · exact noFixedRule_holds
  · exact rulesOutPlainCombinations_holds
  · exact replay_holds

def byAgents {W : Type} (answers : List (Answer W)) : List (Attributed W) :=
  answers.map fun answer => ⟨answer, agentsAnswer⟩

theorem byAgents_answers {W : Type} (answers : List (Answer W)) :
    (byAgents answers).map (·.answer) = answers := by
  simp only [byAgents, List.map_map]
  exact List.map_id _

def dayDeliverable : Deliverable (DayWorld Unit Acorn.Host.Action UInt8 Nat) where
  record := dayCycle
  explanation := dayExplained
  answers := byAgents (dayAnswers (lo := 0) (hi := 1) 0 4)
  keeps := by
    rw [byAgents_answers]
    exact dayCycle_keeps (Obs := UInt8) () Acorn.Host.Action.wait (lo := 0) (hi := 1) (hi' := 2)
      (by decide) (by decide) (by decide) quarterSight_injective 0 4

def hashDeliverable : Deliverable Hashes where
  record := hashes
  explanation := hashesExplained
  answers := byAgents hashAnswers
  keeps := by
    rw [byAgents_answers]
    exact hashes_keeps

def worldInterfaceDeliverable : Deliverable WorldInterface.System where
  record := WorldInterface.worldInterface
  explanation := WorldInterface.worldInterfaceExplained
  answers := []
  keeps := (keeps_iff _ _).mpr fun _ h => nomatch h

def oneStreamDeliverable : Deliverable OneStream.Learner where
  record := OneStream.oneStream
  explanation := OneStream.oneStreamExplained
  answers := []
  keeps := (keeps_iff _ _).mpr fun _ h => nomatch h

end AcornVerif.Intent.Decisions
