/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Perceiving

/-!
# Conditions (b) and (c) in situated form

A class is *situated* when its members are grouped by a situation, the members of one situation
conceal their goals behind that situation's reference world, one action sequence meets at most a
stated number of a situation's members within a visit, and a finite set of members outnumbers the
sum of those numbers. Contract 2's `ConcealedClass`, without its feasibility, is the case of one
situation (`ConcealedClass.situated`).

* `SituatedClass.need`: on every visit, an agent that keeps nothing of its experience solves at
  most the sum, over the situations, of what one action sequence covers there. This is the bound
  of `visits_need`, situation by situation: such an agent may read the situation from its
  percept, and within a situation it is blind. With the margin, that is fewer than the counted
  members.
* `not_situated_of_blindSolvable`: a class one action sequence solves is not situated, however its
  members are grouped. The covers can be had of such a class and the margin cannot.

The witness is the cued doors, `cuedSituated` in `AcornVerif.CuedDoors`: two situations and a
cover of one each, so the bound is two, against four members.

The structure groups members by a label and does not ask that percepts tell the labels apart: a
class whose situations show the same percepts is admitted.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-- The members of a class that are in one situation. -/
abbrev WorldClass.side (family : WorldClass interface) {Situation : Type}
    (situation : family.Index → Situation) (here : Situation) : WorldClass interface where
  Index := {index : family.Index // situation index = here}
  world := fun index => family.world index.1
  start := fun index => family.start index.1

/-- The goals of the members of one situation. -/
def sideOf {family : WorldClass interface} (goals : family.Goals) {Situation : Type}
    (situation : family.Index → Situation) (here : Situation) :
    (family.side situation here).Goals :=
  fun index => goals index.1

/-- **Conditions (b) and (c), situated.** The members are grouped by a situation; the members of
each situation conceal their goals behind that situation's reference world; one action sequence
meets, within a visit, the goals of at most `cover` members of a situation; and some finite set
holds more members than the covers add up to, so that the share of `SituatedClass.need` is small.
Its witness is `cuedSituated`. Its failing examples are `cued_not_one_situation`, which fails the
concealment, and `not_situated_of_blindSolvable` with `lone_not_situated`, which fail the
margin.

The situations are labels of the members, and the structure does not ask that what an agent
perceives tell them apart. It admits a class whose situations show the same percepts, so that the
labels distinguish nothing an agent can observe: `cuedSituated` is such a class when both
situations are given one percept. That impostor is admitted and not kept out. -/
structure SituatedClass (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
    (Situation : Type) [Fintype Situation] where
  /-- The situation of each member. -/
  situation : family.Index → Situation
  /-- The reference world of each situation. -/
  reference : Situation → World interface
  /-- Each reference world's start state. -/
  origin : (here : Situation) → (reference here).State
  /-- Condition (b), within each situation. -/
  conceals : ∀ here, Conceals (family.side situation here) (sideOf goals situation here)
    (reference here) (origin here)
  /-- How many members of a situation one action sequence meets within a visit, at most. -/
  cover : Situation → ℕ
  /-- The covering bound of each situation. -/
  covered : ∀ here, Covered (family.side situation here)
    (visitGoals (sideOf goals situation here) length) (cover here)
  /-- A finite set of members. -/
  members : Finset family.Index
  /-- The margin of condition (c): more members than the situations' covers add up to. -/
  large : ∑ here, cover here < members.card

/-- **The share of a situated class solved without experience.** On every visit, an agent that
keeps nothing of its experience solves at most the sum, over the situations, of the situations'
covers, which is fewer than the class's counted members (`SituatedClass.large`). -/
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

/-- **A class one action sequence solves is not situated**, however its members are grouped: the
sequence meets every member of every situation, so the covers add up to at least the size of every
finite set of members, and the margin of condition (c) cannot hold. -/
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

/-- **A concealed class is the situated class of one situation.** Its reference world is the one
situation's, its covering bound that situation's cover, and its margin the situated margin. -/
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
