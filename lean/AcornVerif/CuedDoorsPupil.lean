/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CuedDoors

/-!
# A learner that reads its situation meets the cued doors

`pupil` keeps one door for each situation. At a visit's start it reads the situation from its
percept and tries that situation's door; shown no success, it changes that door. It solves every
cued door on its second and third visits (`pupil_solves`), so it separates at bound 3 before
visit 2 and retains before visit 3 with no lapse, which no agent driven by the success signal does
(`cued_summary`). The cued doors do not conceal their goals in the full percept behind any one
reference world (`cued_reveals`), so contract 2 (b) as `Conceals` states it excludes them.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-- The pupil: whether its next percept is an outcome, the situation it last read, and the door it
holds for each of the two situations. -/
def pupil (four : 4 ≤ interface.actions.word.toNat) (signal sees : Percept interface → Bool) :
    Agent interface where
  Memory := Bool × Bool × Bool × Bool
  initial := (false, false, false, false)
  act := fun memory percept =>
    match memory with
    | (false, _, first, second) =>
      (key four (sees percept) (bif sees percept then second else first),
        (true, sees percept, first, second))
    | (true, seen, first, second) =>
      (key four false false,
        (false, seen, (bif signal percept || seen then first else !first),
          (bif signal percept || !seen then second else !second)))

/-- At a visit's start the pupil reads the situation and tries the door it holds for it. -/
theorem pupil_ask (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) (signal sees : Percept interface → Bool)
    (reads : ∀ situation, sees (quiet situation) = situation)
    (situation door seen first second : Bool) :
    interact (visits (cued four quiet win situation door) none 1) (pupil four signal sees)
        (((none : Option Bool), (⟨0, Nat.succ_pos 1⟩ : Fin (1 + 1))),
          (false, seen, first, second)) =
      ((some (decide ((key four situation (bif situation then second else first)).val =
          (key four situation door).val)), ⟨1, Nat.lt_succ_self 1⟩),
        (true, situation, first, second)) := by
  have read : sees ((cued four quiet win situation door).percept none) = situation :=
    reads situation
  change ((visits (cued four quiet win situation door) none 1).step
      (none, ⟨0, Nat.succ_pos 1⟩)
      (key four (sees ((cued four quiet win situation door).percept none))
        (bif sees ((cued four quiet win situation door).percept none) then second else first)),
    (true, sees ((cued four quiet win situation door).percept none), first, second)) = _
  rw [read]
  rfl

/-- Shown the outcome, the pupil keeps its doors after a success and changes the door of the
situation it read after a miss; the world returns to its start. -/
theorem pupil_tell (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) (signal sees : Percept interface → Bool) (won : signal win = true)
    (hush : ∀ situation, signal (quiet situation) = false)
    (situation door outcome seen first second : Bool) :
    interact (visits (cued four quiet win situation door) none 1) (pupil four signal sees)
        ((some outcome, (⟨1, Nat.lt_succ_self 1⟩ : Fin (1 + 1))), (true, seen, first, second)) =
      (((none : Option Bool), ⟨0, Nat.succ_pos 1⟩),
        (false, seen, (bif outcome || seen then first else !first),
          (bif outcome || !seen then second else !second))) := by
  have told : signal ((cued four quiet win situation door).percept (some outcome)) = outcome := by
    cases outcome
    · exact hush situation
    · exact won
  change ((visits (cued four quiet win situation door) none 1).step
      (some outcome, ⟨1, Nat.lt_succ_self 1⟩) (key four false false),
    (false, seen,
      (bif signal ((cued four quiet win situation door).percept (some outcome)) || seen
        then first else !first),
      (bif signal ((cued four quiet win situation door).percept (some outcome)) || !seen
        then second else !second))) = _
  rw [told]
  rfl

/-- In every member the pupil's world is at the met outcome after the one step of its second visit
and of its third. -/
theorem pupil_run (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) (signal sees : Percept interface → Bool) (won : signal win = true)
    (hush : ∀ situation, signal (quiet situation) = false)
    (reads : ∀ situation, sees (quiet situation) = situation) (situation door : Bool) :
    (loop (visits (cued four quiet win situation door) none 1) (pupil four signal sees)
        (visitStart (cued four quiet win situation door) none 1) 3).1.1 = some true ∧
      (loop (visits (cued four quiet win situation door) none 1) (pupil four signal sees)
        (visitStart (cued four quiet win situation door) none 1) 5).1.1 = some true := by
  have zero : loop (visits (cued four quiet win situation door) none 1) (pupil four signal sees)
      (visitStart (cued four quiet win situation door) none 1) 0 =
        (((none : Option Bool), ⟨0, Nat.succ_pos 1⟩), (false, false, false, false)) := rfl
  have one : loop (visits (cued four quiet win situation door) none 1) (pupil four signal sees)
      (visitStart (cued four quiet win situation door) none 1) 1 = _ :=
    (congrArg (interact _ _) zero).trans
      (pupil_ask four quiet win signal sees reads situation door false false false)
  have two : loop (visits (cued four quiet win situation door) none 1) (pupil four signal sees)
      (visitStart (cued four quiet win situation door) none 1) 2 = _ :=
    (congrArg (interact _ _) one).trans
      (pupil_tell four quiet win signal sees won hush situation door _ situation false false)
  have three : loop (visits (cued four quiet win situation door) none 1) (pupil four signal sees)
      (visitStart (cued four quiet win situation door) none 1) 3 = _ :=
    (congrArg (interact _ _) two).trans
      (pupil_ask four quiet win signal sees reads situation door situation _ _)
  have fourth : loop (visits (cued four quiet win situation door) none 1) (pupil four signal sees)
      (visitStart (cued four quiet win situation door) none 1) 4 = _ :=
    (congrArg (interact _ _) three).trans
      (pupil_tell four quiet win signal sees won hush situation door _ situation _ _)
  have five : loop (visits (cued four quiet win situation door) none 1) (pupil four signal sees)
      (visitStart (cued four quiet win situation door) none 1) 5 = _ :=
    (congrArg (interact _ _) fourth).trans
      (pupil_ask four quiet win signal sees reads situation door situation _ _)
  rw [three, five]
  cases situation <;> cases door <;> exact ⟨rfl, rfl⟩

/-- **The pupil solves every cued door on its second visit and on its third.** -/
theorem pupil_solves (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) (signal sees : Percept interface → Bool) (won : signal win = true)
    (hush : ∀ situation, signal (quiet situation) = false)
    (reads : ∀ situation, sees (quiet situation) = situation) (index : Bool × Bool) (visit : ℕ)
    (which : visit = 1 ∨ visit = 2) :
    SolvesOnVisit (cuedDoors four quiet win) (cuedGoals four quiet win) 1
      (pupil four signal sees) visit index := by
  have run := pupil_run four quiet win signal sees won hush reads index.1 index.2
  rcases which with first | second
  · subst first
    exact ⟨1, Nat.le_refl 1, Nat.le_refl 1, run.1⟩
  · subst second
    exact ⟨1, Nat.le_refl 1, Nat.le_refl 1, run.2⟩

/-- The four cued doors. -/
def cuedAll : List (Bool × Bool) := [(false, false), (false, true), (true, false), (true, true)]

/-- Every cued door is listed. -/
theorem cuedAll_mem (index : Bool × Bool) : index ∈ cuedAll := by
  obtain ⟨situation, door⟩ := index
  cases situation <;> cases door <;> decide

/-- The four cued doors as a set. -/
def cuedSet : Finset (Bool × Bool) :=
  {(false, false), (false, true), (true, false), (true, true)}

/-- There are more than three cued doors. -/
theorem cuedSet_card : 3 < cuedSet.card := by decide

/-- **The cued doors: who separates and who cannot.** Over an interface with four actions, where
a feedback does not tell the situations apart, a signal shows on the winning percept and on no
situation's percept, and a reading tells the two situations' percepts apart: no agent driven by
that feedback solves more than three members on one of
its first two visits; every experience-free agent solves at most two on any visit; and the pupil
solves all four on its second visit and retains them before visit 3 with no lapse. -/
theorem cued_summary {Φ : Type} (feedback : Percept interface → Φ)
    (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) (canon : Percept interface → Percept interface)
    (keeps : ∀ percept, feedback (canon percept) = feedback percept)
    (flat : ∀ situation, canon (quiet situation) = canon (quiet false))
    (signal sees : Percept interface → Bool) (won : signal win = true)
    (hush : ∀ situation, signal (quiet situation) = false)
    (reads : ∀ situation, sees (quiet situation) = situation) :
    (∀ agent : Agent interface, FeedbackDriven feedback agent → ∀ counted,
      ¬ SeparatesBy (cuedDoors four quiet win) (cuedGoals four quiet win) 1 3 counted 2 agent) ∧
    (∀ agent : Agent interface, ExperienceFree agent → ∀ (visit : ℕ)
      (solved : Finset (Bool × Bool)),
      (∀ index ∈ solved, SolvesOnVisit (cuedDoors four quiet win) (cuedGoals four quiet win) 1
        agent visit index) → solved.card ≤ 2) ∧
    SeparatesBy (cuedDoors four quiet win) (cuedGoals four quiet win) 1 3 cuedAll 2
      (pupil four signal sees) ∧
    RetainsBut (cuedDoors four quiet win) (cuedGoals four quiet win) 1 3 0
      (pupil four signal sees) := by
  refine ⟨fun agent blind counted =>
      (cuedNeeded feedback four quiet win canon keeps flat).need blind counted,
    fun agent free visit solved each => cued_frozen four quiet win free visit solved each,
    ?_, ?_⟩
  · exact ⟨1, cuedSet, by decide, cuedSet_card, fun index _ => ⟨cuedAll_mem index,
      pupil_solves four quiet win signal sees won hush reads index 1 (Or.inl rfl)⟩⟩
  · intro index
    refine ⟨∅, Nat.le_of_eq Finset.card_empty, fun visit later after before _ _ => ?_⟩
    exact pupil_solves four quiet win signal sees won hush reads index later (by omega)

/-- **Contract 2 (b) excludes the cued doors.** Where the two situations' percepts differ, no one
reference world conceals the cued doors' goals in the full percept: at the start, before any goal
is met, members of the two situations already show different percepts. -/
theorem cued_reveals (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) (differ : quiet false ≠ quiet true) (reference : World interface)
    (origin : reference.State) :
    ¬ Conceals (cuedDoors four quiet win) (cuedGoals four quiet win) reference origin := by
  intro hidden
  have first := hidden (false, false) (fun _ => key four false false) 0
    (fun earlier low high => absurd (Nat.le_trans low high) (by decide))
  have second := hidden (true, false) (fun _ => key four false false) 0
    (fun earlier low high => absurd (Nat.le_trans low high) (by decide))
  exact differ (first.trans second.symm)

end AcornVerif.Kernel
