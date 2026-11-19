/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Turns

/-!
# Keeping for an agent that goes on exploring, in a class in turns

`AcornVerif.Kernel.KeepsBut` counts, for every member under every order, the visits on which an
agent that has solved a member fails to solve it again. For an agent that explores with random
draws that count has to be proved under every order, and the orders are too many to go through
one by one. Where the draws an agent consumes depend on what it has learned, the visits on which
it explores depend on the order, and no count of them under every order follows from the
generator alone (argued; no theorem states it).

`KeepsOn` is the part of keeping that is a statement about each run and counts nothing: under
every order, a member solved on a visit is solved on every later visit before the horizon that
brings the same situation and that a predicate `admits` for that member under that order. No
lapse is allowed on an admitted visit. The predicate to read is that the agent takes no
exploratory action on that visit. The count of admitted visits is asked where a prover can
count, inside the promise of mastery (`AcornVerif.Kernel.MastersGridBy`).

An agent that keeps with no lapse keeps on every predicate (`KeepsBut.on`).

A degenerate instance, read for what it says: `KeepsOn` is vacuous for a member and order on
whose visits the predicate never holds, and with the predicate that admits no visit every agent
meets it (`keepsOn_of_never`). It says something only together with a count of admitted visits.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface} {family : TurnClass interface} {goals : family.Goals}
  {length : ℕ}

/-- **Keeping on the visits a predicate admits.** Under every order, a member the agent has
solved on a visit it solves on every later visit before the visit `horizon` that brings the same
situation and that the predicate admits for that member under that order. -/
def KeepsOn (family : TurnClass interface) (goals : family.Goals) (length horizon : ℕ)
    (admits : family.Index → (ℕ → Bool) → ℕ → Prop) (agent : Agent interface) : Prop :=
  ∀ (index : family.Index) (order : ℕ → Bool) (visit later : ℕ), visit < later →
    later < horizon → order later = order visit →
    SolvesTurn family goals length order agent visit index → admits index order later →
      SolvesTurn family goals length order agent later index

variable {horizon : ℕ} {admits : family.Index → (ℕ → Bool) → ℕ → Prop} {agent : Agent interface}

/-- An agent that keeps with no lapse keeps on the visits of every predicate. -/
theorem KeepsBut.on (keeps : KeepsBut family goals length horizon 0 agent)
    (admits : family.Index → (ℕ → Bool) → ℕ → Prop) :
    KeepsOn family goals length horizon admits agent := by
  intro index order visit later after before same solved _
  obtain ⟨lapsed, count, kept⟩ := keeps index order
  have none : lapsed = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp count)
  exact kept visit later after before same solved (by rw [none]; exact Finset.notMem_empty later)

/-- Where a predicate admits no visit, every agent keeps on its visits: keeping on admitted
visits says nothing without a count of them. -/
theorem keepsOn_of_never (family : TurnClass interface) (goals : family.Goals)
    (length horizon : ℕ) (agent : Agent interface) :
    KeepsOn family goals length horizon (fun _ _ _ => False) agent :=
  fun _ _ _ _ _ _ _ _ never => never.elim

end AcornVerif.Kernel
