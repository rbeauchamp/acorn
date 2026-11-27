import AcornVerif.Perceiving

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

abbrev WorldClass.side (family : WorldClass interface) {Situation : Type}
    (situation : family.Index → Situation) (here : Situation) : WorldClass interface where
  Index := {index : family.Index // situation index = here}
  world := fun index => family.world index.1
  start := fun index => family.start index.1

def sideOf {family : WorldClass interface} (goals : family.Goals) {Situation : Type}
    (situation : family.Index → Situation) (here : Situation) :
    (family.side situation here).Goals :=
  fun index => goals index.1

structure SituatedClass (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
    (Situation : Type) [Fintype Situation] where
  situation : family.Index → Situation
  reference : Situation → World interface
  origin : (here : Situation) → (reference here).State
  conceals : ∀ here, Conceals (family.side situation here) (sideOf goals situation here)
    (reference here) (origin here)
  cover : Situation → ℕ
  covered : ∀ here, Covered (family.side situation here)
    (visitGoals (sideOf goals situation here) length) (cover here)
  members : Finset family.Index
  large : ∑ here, cover here < members.card

theorem SituatedClass.need {family : WorldClass interface} {goals : family.Goals} {length : ℕ}
    {Situation : Type} [Fintype Situation]
    (situated : SituatedClass family goals length Situation) {agent : Agent interface}
    (free : ExperienceFree agent) (visit : ℕ) (solved : Finset family.Index)
    (each : ∀ index ∈ solved, SolvesOnVisit family goals length agent visit index) :
    solved.card ≤ ∑ here, situated.cover here := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := situated.situation) (t := Finset.univ)
    (fun index _ => Finset.mem_univ _)]
  refine Finset.sum_le_sum (fun here _ => ?_)
  rw [← Finset.card_subtype]
  exact visits_need (situated.conceals here) (situated.covered here) free visit
    (solved.subtype fun index => situated.situation index = here)
    (fun index member => each index.1 (Finset.mem_subtype.mp member))

theorem not_situated_of_blindSolvable {family : WorldClass interface} {goals : family.Goals}
    {length : ℕ} {Situation : Type} [Fintype Situation] (actions : ℕ → Act interface)
    (solves : ∀ index, (visitGoals goals length index).MetBy (family.start index) actions) :
    IsEmpty (SituatedClass family goals length Situation) :=
  ⟨fun situated => by
    classical
    have few : situated.members.card ≤ ∑ here, situated.cover here := by
      rw [Finset.card_eq_sum_card_fiberwise (f := situated.situation) (t := Finset.univ)
        (fun index _ => Finset.mem_univ _)]
      refine Finset.sum_le_sum (fun here _ => ?_)
      rw [← Finset.card_subtype]
      exact situated.covered here actions
        (situated.members.subtype fun index => situated.situation index = here)
        (fun index _ => solves index.1)
    exact absurd situated.large (Nat.not_lt.mpr few)⟩

def ConcealedClass.situated {family : WorldClass interface} {goals : family.Goals}
    {length bound : ℕ} (concealed : ConcealedClass family goals length bound) :
    SituatedClass family goals length Unit where
  situation := fun _ => ()
  reference := fun _ => concealed.reference
  origin := fun _ => concealed.origin
  conceals := fun _ index actions time unmet => concealed.conceals index.1 actions time unmet
  cover := fun _ => bound
  covered := by
    intro _ actions solved each
    have all := concealed.covered actions (solved.map ⟨Subtype.val, Subtype.val_injective⟩)
      (fun index member => by
        obtain ⟨inside, chosen, rfl⟩ := Finset.mem_map.mp member
        exact each inside chosen)
    rwa [Finset.card_map] at all
  members := concealed.members
  large := by simpa using concealed.large

end AcornVerif.Kernel
