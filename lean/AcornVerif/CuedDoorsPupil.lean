import AcornVerif.CuedDoors

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

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

theorem cuedAll_card : 3 < cuedAll.toFinset.card := by decide

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
    fun agent free visit solved each => cued_need four quiet win free visit solved each,
    ?_, ?_⟩
  · exact ⟨1, cuedAll.toFinset, by decide, cuedAll_card, fun index _ => ⟨cuedAll_mem index,
      pupil_solves four quiet win signal sees won hush reads index 1 (Or.inl rfl)⟩⟩
  · intro index
    refine ⟨∅, Nat.le_of_eq Finset.card_empty, fun visit later after before _ _ => ?_⟩
    exact pupil_solves four quiet win signal sees won hush reads index later (by omega)

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
