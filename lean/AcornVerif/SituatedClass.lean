/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CuedDoorsPupil

/-!
# Conditions (b) and (c) in situated form

A class is *situated* when its members are grouped by a situation, the members of one situation
conceal their goals behind that situation's reference world, and one action sequence meets at
most a stated number of a situation's members within a visit. Contract 2's `Conceals` with
`Covered` is the case of one situation.

* `SituatedClass.need`: on every visit, an agent that keeps nothing of its experience solves at
  most the sum, over the situations, of what one action sequence covers there. This is the bound
  of `visits_need`, situation by situation: such an agent may read the situation from its
  percept, and within a situation it is blind.
* `cuedSituated`: the cued doors are situated, with two situations and a cover of one each, so
  the bound is two.
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
each situation conceal their goals behind that situation's reference world; and one action
sequence meets, within a visit, the goals of at most `cover` members of a situation. Its witness
is `cuedSituated` and its failing example `cued_not_one_situation`. -/
structure SituatedClass (family : WorldClass interface) (goals : family.Goals) (length : ℕ)
    (Situation : Type) where
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

/-- **The frozen share of a situated class.** On every visit, an agent that keeps nothing of its
experience solves at most the sum, over the situations, of the situations' covers. -/
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

/-- **The cued doors are situated**: two situations, each concealing its two doors behind the
world that shows that situation's percept, and one action meets one door. -/
def cuedSituated (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) :
    SituatedClass (cuedDoors four quiet win) (cuedGoals four quiet win) 1 Bool where
  situation := fun (index : Bool × Bool) => index.1
  reference := fun here => firstActionWorld interface (quiet here)
  origin := fun _ => none
  conceals := by
    rintro here ⟨⟨situation, door⟩, inside⟩ actions time unmet
    have same : situation = here := inside
    subst same
    have still : path (cued four quiet win situation door) none actions time ≠ some true := by
      cases time with
      | zero =>
        intro wrong
        have bad : (none : Option Bool) = some true := wrong
        cases bad
      | succ time =>
        exact unmet (time + 1) (Nat.succ_le_succ (Nat.zero_le time)) (Nat.le_refl _)
    exact cued_quiet four quiet win situation door _ still
  cover := fun _ => 1
  covered := by
    intro here actions solved each
    refine Finset.card_le_one.mpr (fun first inFirst second inSecond => ?_)
    have keyFirst := cued_met four quiet win first.1 actions (each first inFirst)
    have keySecond := cued_met four quiet win second.1 actions (each second inSecond)
    obtain ⟨situation, door⟩ := key_inj four (keyFirst.symm.trans keySecond)
    exact Subtype.ext (Prod.ext situation door)

/-- In the cued doors an agent that keeps nothing solves at most two members on any visit, by the
situated bound. -/
theorem cued_need (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) {agent : Agent interface} (free : ExperienceFree agent)
    (visit : ℕ) (solved : Finset (Bool × Bool))
    (each : ∀ index ∈ solved, SolvesOnVisit (cuedDoors four quiet win)
      (cuedGoals four quiet win) 1 agent visit index) :
    solved.card ≤ 2 :=
  (cuedSituated four quiet win).need free visit solved each

end AcornVerif.Kernel
