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

This module states keeping in the two parts the postcondition's reading of 2026-11-17 has, placed
so that each part can be proved.

- `KeepsOn`: under every order, a member solved on a visit is solved on every later visit before
  the horizon that brings the same situation and that a predicate `admits` for that member under
  that order. No lapse is allowed on an admitted visit. The predicate to read is that the agent
  takes no exploratory action on that visit. This part is a statement about each run and counts
  nothing, so it is asked under every order.
- `MastersCalmBy`: mastery, as `AcornVerif.Kernel.MastersBy` states it, together with a count:
  for each mastered member and each situation of the visit of mastery, the predicate admits every
  visit of that run before the horizon but for at most `lapses`. This part counts, and it is
  asked of the finitely many runs of mastery, where a prover can count.

Together they give keeping but for the lapses on the runs of mastery (`MastersCalmBy.kept`): each
mastered member is solved again, in each of its two runs, on every later visit before the horizon
that brings the same situation, but for at most `lapses` visits. So the pair is not vacuous
where the limit leaves more later visits than the lapses.

`MastersCalmBy` gives `MastersBy` (`MastersCalmBy.masters`), so everything that excludes an agent
from mastery excludes it here. An agent that keeps with no lapse keeps on every predicate
(`KeepsBut.on`), and an agent that masters masters with room under the predicate that admits
every visit (`MastersBy.calm`).

What the count's place leaves open. `KeepsOn` is vacuous for a member and order on whose visits
the predicate never holds. Under an order outside the runs of mastery nothing here bounds how
often that is. For the executed agent the predicate is decided by its declared exploration draw,
so an agent can make it fail more often only by steering which generator word the draw reads.
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

/-- **Mastery with room.** Under one order, on one visit before the visit `limit`, the agent
solves each member of a set of more than `bound` members with different keys in both situations,
and in each of those two runs of each such member the predicate admits every visit before the
visit `horizon` but for at most `lapses`. -/
def MastersCalmBy (family : TurnClass interface) (goals : family.Goals) (length bound : ℕ)
    {κ : Type} (key : family.Index → κ) (limit horizon lapses : ℕ)
    (admits : family.Index → (ℕ → Bool) → ℕ → Prop) (agent : Agent interface) : Prop :=
  ∃ (order : ℕ → Bool) (visit : ℕ) (solved : Finset family.Index),
    visit < limit ∧ bound < solved.card ∧
    (∀ first ∈ solved, ∀ second ∈ solved, key first = key second → first = second) ∧
    ∀ index ∈ solved, ∀ situation : Bool,
      SolvesTurn family goals length (Function.update order visit situation) agent visit
        index ∧
      ∃ restless : Finset ℕ, restless.card ≤ lapses ∧
        ∀ other, other < horizon → other ∉ restless →
          admits index (Function.update order visit situation) other

variable {κ : Type} {key : family.Index → κ} {bound limit horizon lapses : ℕ}
  {admits : family.Index → (ℕ → Bool) → ℕ → Prop} {agent : Agent interface}

/-- Mastery with room is mastery. -/
theorem MastersCalmBy.masters
    (masters : MastersCalmBy family goals length bound key limit horizon lapses admits agent) :
    MastersBy family goals length bound key limit agent := by
  obtain ⟨order, visit, solved, before, many, distinct, each⟩ := masters
  exact ⟨order, visit, solved, before, many, distinct,
    fun index member situation => (each index member situation).1⟩

/-- An agent that masters, masters with room under the predicate that admits every visit. -/
theorem MastersBy.calm (masters : MastersBy family goals length bound key limit agent)
    (horizon lapses : ℕ) :
    MastersCalmBy family goals length bound key limit horizon lapses (fun _ _ _ => True)
      agent := by
  obtain ⟨order, visit, solved, before, many, distinct, each⟩ := masters
  exact ⟨order, visit, solved, before, many, distinct, fun index member situation =>
    ⟨each index member situation, ∅, Nat.zero_le lapses, fun _ _ _ => trivial⟩⟩

/-- An agent that keeps with no lapse keeps on the visits of every predicate. -/
theorem KeepsBut.on (keeps : KeepsBut family goals length horizon 0 agent)
    (admits : family.Index → (ℕ → Bool) → ℕ → Prop) :
    KeepsOn family goals length horizon admits agent := by
  intro index order visit later after before same solved _
  obtain ⟨lapsed, count, kept⟩ := keeps index order
  have none : lapsed = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp count)
  exact kept visit later after before same solved (by rw [none]; exact Finset.notMem_empty later)

/-- **The two parts give keeping but for the lapses, on the runs of mastery.** An agent that
masters with room and keeps on the admitted visits solves each mastered member again, in each of
the two runs of the visit of mastery, on every later visit before the horizon that brings the
situation of that run's visit of mastery, but for at most `lapses` visits. -/
theorem MastersCalmBy.kept
    (masters : MastersCalmBy family goals length bound key limit horizon lapses admits agent)
    (keeps : KeepsOn family goals length horizon admits agent) :
    ∃ (order : ℕ → Bool) (visit : ℕ) (solved : Finset family.Index),
      visit < limit ∧ bound < solved.card ∧
      ∀ index ∈ solved, ∀ situation : Bool, ∃ lapsed : Finset ℕ, lapsed.card ≤ lapses ∧
        ∀ later, visit < later → later < horizon →
          Function.update order visit situation later = situation → later ∉ lapsed →
            SolvesTurn family goals length (Function.update order visit situation) agent later
              index := by
  obtain ⟨order, visit, solved, before, many, -, each⟩ := masters
  refine ⟨order, visit, solved, before, many, fun index member situation => ?_⟩
  obtain ⟨once, restless, count, admitted⟩ := each index member situation
  refine ⟨restless, count, fun later after within same out => ?_⟩
  exact keeps index (Function.update order visit situation) visit later after within
    (same.trans (Function.update_self visit situation order).symm) once
    (admitted later within out)

/-- Where a predicate admits no visit, every agent keeps on its visits: keeping on admitted
visits says nothing without a count of them. -/
theorem keepsOn_of_never (family : TurnClass interface) (goals : family.Goals)
    (length horizon : ℕ) (agent : Agent interface) :
    KeepsOn family goals length horizon (fun _ _ _ => False) agent :=
  fun _ _ _ _ _ _ _ _ never => never.elim

end AcornVerif.Kernel
