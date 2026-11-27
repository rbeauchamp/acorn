import AcornVerif.Turns

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {family : TurnClass interface} {goals : family.Goals}
  {length : ℕ}

def KeepsOn (family : TurnClass interface) (goals : family.Goals) (length horizon : ℕ)
    (admits : family.Index → (ℕ → Bool) → ℕ → Prop) (agent : Agent interface) : Prop :=
  ∀ (index : family.Index) (order : ℕ → Bool) (visit later : ℕ), visit < later →
    later < horizon → order later = order visit →
    SolvesTurn family goals length order agent visit index → admits index order later →
      SolvesTurn family goals length order agent later index

variable {horizon : ℕ} {admits : family.Index → (ℕ → Bool) → ℕ → Prop} {agent : Agent interface}

theorem KeepsBut.on (keeps : KeepsBut family goals length horizon 0 agent)
    (admits : family.Index → (ℕ → Bool) → ℕ → Prop) :
    KeepsOn family goals length horizon admits agent := by
  intro index order visit later after before same solved _
  obtain ⟨lapsed, count, kept⟩ := keeps index order
  have none : lapsed = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp count)
  exact kept visit later after before same solved (by rw [none]; exact Finset.notMem_empty later)

theorem keepsOn_of_never (family : TurnClass interface) (goals : family.Goals)
    (length horizon : ℕ) (agent : Agent interface) :
    KeepsOn family goals length horizon (fun _ _ _ => False) agent :=
  fun _ _ _ _ _ _ _ _ never => never.elim

end AcornVerif.Kernel
