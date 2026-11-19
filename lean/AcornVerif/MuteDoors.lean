/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CuedDoorsPupil

/-!
# Failing examples for the kernel's forms of contract 2 and the postcondition

* `muteConcealed`, `mute_unlearnable`: the kernel's `ConcealedClass`, conditions (a) to (c), holds
  of a class of two members that show one percept at every state. In it no agent solves both
  members on any visit, so no agent ever exceeds the covering bound: the class meets (a) to (c)
  and nothing can be learned in it. This is the obstruction `docs/mission-contract.md` argues
  under contract 2, machine-checked. The intent record of contract 2 excludes the class by its
  clause that success shows.
* `mute_not_decides`: the same class fails condition (e), `PerceivingDecides`, for separation at
  its covering bound. No agent separates there, so perceiving is needed with nothing to exclude and
  no agent that reads its observation does better.
* `ExperienceFree.not_separatesBy`: an agent that keeps nothing never separates from a covering
  bound in a class that conceals its goals.
* `fickle_forgets`: an agent that solves a cued door on its first visit and not on its second,
  which fails retention before visit 2 with no lapse.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-! ## Big by (a) to (c), with nothing to learn -/

/-- One of two different actions. -/
def pick (two : 2 ≤ interface.actions.word.toNat) (door : Bool) : Act interface :=
  match door with
  | false => ⟨0, by omega⟩
  | true => ⟨1, by omega⟩

/-- The two picked actions differ. -/
theorem pick_differ (two : 2 ≤ interface.actions.word.toNat) :
    (pick two false).val ≠ (pick two true).val :=
  fun same => Nat.zero_ne_one same

/-- There are two doors. -/
theorem two_doors : 1 < ({false, true} : Finset Bool).card := by decide

/-- The mute doors: two members, each the world that shows one percept at every state and records
the first action it receives. -/
abbrev mute (interface : Interface) (shown : Percept interface) : WorldClass interface where
  Index := Bool
  world := fun _ => firstActionWorld interface shown
  start := fun _ => (none : Option (Act interface))

/-- A mute door's goal: its own action was the first, within one step. -/
def muteGoals (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    (mute interface shown).Goals :=
  fun door => ⟨fun (state : Option (Act interface)) => state = some (pick two door), 1⟩

/-- A mute door's goal is met within a visit of one step exactly by its own action first. -/
theorem mute_met (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface)
    (door : Bool) (actions : ℕ → Act interface)
    (met : (visitGoals (muteGoals two shown) 1 door).MetBy ((mute interface shown).start door)
      actions) : actions 0 = pick two door := by
  obtain ⟨time, low, high, reached⟩ := met
  have one : time = 1 := Nat.le_antisymm high low
  subst one
  have outcome : some (actions 0) = some (pick two door) := reached
  exact Option.some.inj outcome

/-- **The mute doors are big by conditions (a) to (c)**, with visits of one step and the covering
bound one. -/
def muteConcealed (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    ConcealedClass (mute interface shown) (muteGoals two shown) 1 1 where
  reference := firstActionWorld interface shown
  origin := none
  conceals := fun _ _ _ _ => rfl
  covered := by
    intro actions solved each
    refine Finset.card_le_one.mpr (fun first inFirst second inSecond => ?_)
    have same := (mute_met two shown first actions (each first inFirst)).symm.trans
      (mute_met two shown second actions (each second inSecond))
    cases first <;> cases second
    · rfl
    · exact absurd (congrArg Fin.val same) (pick_differ two)
    · exact absurd (congrArg Fin.val same).symm (pick_differ two)
    · rfl
  feasible := fun door => ⟨fun _ => pick two door, 1, Nat.le_refl 1, Nat.le_refl 1, rfl⟩
  members := {false, true}
  large := two_doors

/-- **In the mute doors no agent solves both members on any visit.** Its runs in the two members
are one run, so on each visit it takes one first action. No agent separates from the covering
bound there, whatever it keeps of its experience. -/
theorem mute_unlearnable (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface)
    (agent : Agent interface) (visit : ℕ) :
    ¬ (SolvesOnVisit (mute interface shown) (muteGoals two shown) 1 agent visit false ∧
      SolvesOnVisit (mute interface shown) (muteGoals two shown) 1 agent visit true) := by
  rintro ⟨⟨stepFirst, lowFirst, highFirst, metFirst⟩, ⟨stepSecond, lowSecond, highSecond,
    metSecond⟩⟩
  have oneFirst : stepFirst = 1 := Nat.le_antisymm highFirst lowFirst
  have oneSecond : stepSecond = 1 := Nat.le_antisymm highSecond lowSecond
  subst oneFirst oneSecond
  have same : some (pick two false) = some (pick two true) := metFirst.symm.trans metSecond
  exact absurd (congrArg Fin.val (Option.some.inj same)) (pick_differ two)

/-- So no agent separates from the mute doors' covering bound, before any visit. -/
theorem mute_no_separation (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface)
    (agent : Agent interface) (counted : List Bool) (limit : ℕ) :
    ¬ SeparatesBy (mute interface shown) (muteGoals two shown) 1 1 counted limit agent := by
  rintro ⟨visit, solved, -, many, each⟩
  have both : ∀ door : Bool, door ∈ solved := by
    intro door
    by_contra missing
    have small : solved ⊆ ({!door} : Finset Bool) := by
      intro other member
      have differ : other ≠ door := fun same => missing (same ▸ member)
      exact Finset.mem_singleton.mpr (by cases other <;> cases door <;> simp_all)
    have few := Finset.card_le_card small
    rw [Finset.card_singleton] at few
    omega
  exact mute_unlearnable two shown agent visit
    ⟨(each false (both false)).2, (each true (both true)).2⟩

/-- **The mute doors fail condition (e), though perceiving is needed in them.** For every
feedback, no agent whose effect on every run of the class is that of a clock-and-feedback agent
separates from the covering bound there, because no agent does. The negative half of the condition
holds with nothing to exclude, and no agent that reads its observation does better. -/
theorem mute_not_decides {Φ : Type} (feedback : Percept interface → Φ)
    (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface) (counted : List Bool)
    (limit : ℕ) :
    PerceivingNeeded feedback (visitRuns (mute interface shown) 1)
        (SeparatesBy (mute interface shown) (muteGoals two shown) 1 1 counted limit) ∧
      ¬ PerceivingDecides feedback (visitRuns (mute interface shown) 1)
        (SeparatesBy (mute interface shown) (muteGoals two shown) 1 1 counted limit) :=
  not_decides_of_unmet feedback _
    (fun agent => mute_no_separation two shown agent counted limit)

/-! ## Separation and retention -/

variable {family : WorldClass interface} {goals : family.Goals}
  {reference : World interface} {origin : reference.State}

/-- **An agent that keeps nothing never separates** from a covering bound, in a class that
conceals its goals. -/
theorem ExperienceFree.not_separatesBy {agent : Agent interface} (free : ExperienceFree agent)
    (hidden : Conceals family goals reference origin) {length bound : ℕ}
    (covered : Covered family (visitGoals goals length) bound) (counted : List family.Index)
    (limit : ℕ) : ¬ SeparatesBy family goals length bound counted limit agent := by
  rintro ⟨visit, solved, -, many, each⟩
  exact absurd many (Nat.not_lt.mpr (visits_need hidden covered free visit solved
    (fun index member => (each index member).2)))

/-- An agent that tries the first cued door's key at its first step and the second door's key at
every later step, reading nothing. -/
def fickle (four : 4 ≤ interface.actions.word.toNat) : Agent interface where
  Memory := ℕ
  initial := 0
  act := fun count _ => (if count = 0 then key four false false else key four false true, count + 1)

/-- **The fickle agent solves a cued door once and not again**, so it does not retain before
visit 2 with no lapse. -/
theorem fickle_forgets (four : 4 ≤ interface.actions.word.toNat) (quiet : Bool → Percept interface)
    (win : Percept interface) :
    SolvesOnVisit (cuedDoors four quiet win) (cuedGoals four quiet win) 1 (fickle four) 0
        (false, false) ∧
      ¬ RetainsBut (cuedDoors four quiet win) (cuedGoals four quiet win) 1 2 0 (fickle four) := by
  have first : SolvesOnVisit (cuedDoors four quiet win) (cuedGoals four quiet win) 1 (fickle four)
      0 (false, false) := ⟨1, Nat.le_refl 1, Nat.le_refl 1, rfl⟩
  refine ⟨first, fun retains => ?_⟩
  obtain ⟨lapsed, none, keeps⟩ := retains (false, false)
  have empty : lapsed = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp none)
  obtain ⟨step, low, high, met⟩ := keeps 0 1 (by decide) (by decide) first (by rw [empty]; simp)
  have one : step = 1 := Nat.le_antisymm high low
  subst one
  have outcome : (some false : Option Bool) = some true := met
  cases outcome

end AcornVerif.Kernel
