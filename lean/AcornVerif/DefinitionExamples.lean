/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.AgentInside
import AcornVerif.Persistence
import AcornVerif.PressWorld
import AcornVerif.SituatedClass

/-!
# The missing halves: a witness or a failing example for each definition that had only one

Each definition of the review of Acorn's semantics is meant to come with a witness that meets it
and an example that fails it for the reason it exists. This module supplies the half that the
modules of the definitions leave out.

* `HoldsFinitely`: `visitScript_holdsFinitely` is a witness.
* `SituatedClass`: `cued_not_one_situation` is a failing example of its concealment, the cued
  doors read as one situation, and `lone_not_situated` one of its margin, a class that has the
  covers and that one action sequence solves.
* `BeyondCapacity`: `not_beyond_of_blindSolvable` is a failing example, a class one action
  sequence solves. Its witness is a class of the grid world, in
  `AcornVerif.CurrentConcealedTargetCapacity`.
* `ActionsDistinct`: `tally_actionsDistinct` is a witness, with two different actions.
* `RunsAsDriven`: `pupil_not_runsAsDriven` is a failing example.
* `ReadsObservation`: `pupil_reads` is a witness.
* `StopsLearningAt`: `pupil_stops` is a witness and `pupil_goes_on` a failing example, both under
  the pupil's declaration of its two doors as what it has learned. Under the empty declaration
  every agent is a witness (`nothing_stops`).
* `FeedbackDriven`: `pupil_not_feedbackDriven` is a failing example; every agent stepped by the
  feedback is a witness (`Stepped.feedbackDriven`).
* `Apart` and `Mute`, the two halves of forks in time: `oneStart_not_apart` and `twoTone_not_mute`
  are failing examples; the day-and-night class of the grid world is their witness.
-/

namespace AcornVerif.Kernel
open Acorn Acorn.Features

variable {interface : Interface}

/-- **A witness of `HoldsFinitely`.** The script that restarts with every visit holds one of
finitely many memories in every world. -/
theorem visitScript_holdsFinitely (length : ℕ) (actions : ℕ → Act interface)
    (world : World interface) (start : world.State) :
    HoldsFinitely world (visitScript interface length actions) start :=
  ⟨List.finRange (length + 1), fun _ => List.mem_finRange _⟩

/-- **A failing example of `SituatedClass`, by its concealment.** Read as a class of one
situation, the cued doors are not situated where the two situations' percepts differ: members of
both would have to show one reference world's percept at the start. -/
theorem cued_not_one_situation (four : 4 ≤ interface.actions.word.toNat)
    (quiet : Bool → Percept interface) (win : Percept interface)
    (differ : quiet false ≠ quiet true) :
    IsEmpty (SituatedClass (cuedDoors four quiet win) (cuedGoals four quiet win) 1 Unit) :=
  ⟨fun situated => by
    have first := situated.conceals () ⟨(false, false), Subsingleton.elim _ _⟩
      (fun _ => key four false false) 0
      (fun earlier low high => absurd (Nat.le_trans low high) (by decide))
    have second := situated.conceals () ⟨(true, false), Subsingleton.elim _ _⟩
      (fun _ => key four false false) 0
      (fun earlier low high => absurd (Nat.le_trans low high) (by decide))
    exact differ (first.trans second.symm)⟩

/-- **A failing example of `SituatedClass`, by its margin.** One mute door alone has the covers:
it conceals its goal behind its own world, and one action sequence meets at most one member, there
being one. It is not situated, however its member is grouped, because that sequence solves the
whole class: an agent that keeps nothing solves all of it on every visit, and the covers add up to
no fewer than its members. -/
theorem lone_not_situated (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface)
    (Situation : Type) [Fintype Situation] :
    Conceals ((mute interface shown).side id false) (sideOf (muteGoals two shown) id false)
        (firstActionWorld interface shown) none ∧
      Covered ((mute interface shown).side id false)
        (visitGoals (sideOf (muteGoals two shown) id false) 1) 1 ∧
      IsEmpty (SituatedClass ((mute interface shown).side id false)
        (sideOf (muteGoals two shown) id false) 1 Situation) := by
  refine ⟨fun _ _ _ _ => rfl, fun _ solved _ => Finset.card_le_one.mpr
    (fun first _ second _ => Subtype.ext (first.2.trans second.2.symm)),
    not_situated_of_blindSolvable (fun _ => pick two false) ?_⟩
  rintro ⟨door, inside⟩
  have same : door = false := inside
  subst same
  exact ⟨1, Nat.le_refl 1, Nat.le_refl 1, rfl⟩

/-- **A failing example of `BeyondCapacity`.** A class one action sequence solves is beyond no
bound, at any number of slots and any margin: the sequence covers every member, so the count
cannot hold. A class of copies of one problem is such a class. -/
theorem not_beyond_of_blindSolvable {family : WorldClass interface} {goals : family.Goals}
    {length slots bits margin : ℕ} (actions : ℕ → Act interface)
    (solves : ∀ index, (visitGoals goals length index).MetBy (family.start index) actions) :
    IsEmpty (BeyondCapacity family goals length slots bits margin) :=
  ⟨fun beyond => by
    have few := blindSolvable_covered actions solves beyond.covered beyond.members
    have powers := Nat.pow_le_pow_left few (slots + 1)
    have wide : beyond.members.card ^ (slots + 1) ≤
        2 ^ (bits + margin) * beyond.cover ^ (slots + 1) :=
      powers.trans (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (by positivity)))
    exact absurd beyond.beyond (Nat.not_lt.mpr wide)⟩

/-- **A witness of `ActionsDistinct`, within the interface's actions.** In the world that counts
its steps, the policy that asks one action at step one and another elsewhere asks two different
actions along every action sequence. -/
theorem tally_actionsDistinct (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    ActionsDistinct (tallyWorld interface shown) (0 : ℕ)
      (fun (state : ℕ) => pick two (decide (state = 1))) 2 := by
  intro actions
  refine ⟨fun index => index.val, fun first second differ same => ?_⟩
  rw [tally_path, tally_path] at same
  have values : (pick two (decide (first.val = 1))).val =
      (pick two (decide (second.val = 1))).val := congrArg Fin.val same
  have apart : first.val ≠ second.val := fun equal => differ (Fin.ext equal)
  have low := first.isLt
  have high := second.isLt
  rcases Nat.lt_or_ge first.val 1 with small | large
  · have zero : first.val = 0 := by omega
    have one : second.val = 1 := by omega
    rw [zero, one] at values
    exact pick_differ two values
  · have one : first.val = 1 := by omega
    have zero : second.val = 0 := by omega
    rw [one, zero] at values
    exact pick_differ two values.symm

/-- **A failing example of `RunsAsDriven`.** In the cued doors the pupil's effect is not that of
a clock-and-reward agent: it separates where no agent with that effect does. -/
theorem pupil_not_runsAsDriven (four : 4 ≤ interface.actions.word.toNat)
    (shown : Percept interface) :
    ¬ RunsAsDriven (fun percept : Percept interface => percept.reward)
      (visitRuns (cuedDoors four (cuePercept shown) (winPercept shown)) 1)
      (pupil four paid cue) :=
  fun driven => (cued_perceiving four shown).1 _ driven (cued_reward four shown).2.2.1

/-- **A witness of `ReadsObservation`.** The pupil reads its observation beyond its reward. -/
theorem pupil_reads (four : 4 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    ReadsObservation (fun percept : Percept interface => percept.reward) (pupil four paid cue) :=
  (pupil_learnsAt four shown).reads

/-- **A failing example of `FeedbackDriven`.** The pupil's actions do not depend on its clock and
its reward words alone. -/
theorem pupil_not_feedbackDriven (four : 4 ≤ interface.actions.word.toNat)
    (shown : Percept interface) :
    ¬ FeedbackDriven (fun percept : Percept interface => percept.reward) (pupil four paid cue) :=
  fun blind => pupil_not_runsAsDriven four shown (blind.runsAsDriven _)

/-! ## Forks in time: what fails each half -/

/-- A class in turns with one member whose two situations are one start state: the world that
shows one percept and records the first action it receives. -/
abbrev oneStart (interface : Interface) (shown : Percept interface) : TurnClass interface where
  Index := Unit
  world := fun _ => firstActionWorld interface shown
  start := fun _ _ => (none : Option (Act interface))

/-- The goal of the one-start class: a given action was the first, within one step. -/
def oneStartGoals (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    (oneStart interface shown).Goals :=
  fun _ => ⟨fun (state : Option (Act interface)) => state = some (pick two false), 1⟩

/-- **A failing example of `Apart`.** A member whose two situations are one start state is no
fork: the one action sequence that meets its goal from the one start meets it from the other. -/
theorem oneStart_not_apart (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    ¬ Apart (oneStart interface shown) (oneStartGoals two shown) 1 :=
  fun apart => apart () (fun _ => pick two false)
    ⟨⟨1, Nat.le_refl 1, Nat.le_refl 1, rfl⟩, ⟨1, Nat.le_refl 1, Nat.le_refl 1, rfl⟩⟩

/-- A world that stays in one of two states and shows a different reward word in each. -/
def twoToneWorld (shown : Percept interface) : World interface where
  State := Bool
  step := fun state _ => state
  percept := fun state => bif state then winPercept shown else cuePercept shown false

/-- A class in turns with one member, whose two situations are the two states of the two-tone
world. -/
abbrev twoTone (shown : Percept interface) : TurnClass interface where
  Index := Unit
  world := fun _ => twoToneWorld shown
  start := fun _ situation => situation

/-- The goal of the two-tone class is never met. -/
def twoToneGoals (shown : Percept interface) : (twoTone shown).Goals :=
  fun _ => ⟨fun _ => False, 1⟩

/-- **A failing example of `Mute`.** Situations that the feedback tells apart are not silent: in
the two-tone class the reward word differs between the two situations before any goal is met, so
an agent that reads only its reward can tell which situation a visit brings. -/
theorem twoTone_not_mute (two : 2 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    ¬ Mute (fun percept : Percept interface => percept.reward) (twoTone shown)
      (twoToneGoals shown) :=
  fun mute => zero_ne_one (mute () (fun _ => pick two false) 0
    (fun _ _ _ wrong => wrong) (fun _ _ _ wrong => wrong))

/-! ## Stopping, and not stopping, to learn -/

/-- In the cued door whose door the pupil holds from the start, the pupil's run alternates between
two states of the world and its memory. -/
theorem pupil_settled (four : 4 ≤ interface.actions.word.toNat) (shown : Percept interface)
    (time : ℕ) :
    loop (visits (cued four (cuePercept shown) (winPercept shown) false false) none 1)
        (pupil four paid cue)
        (visitStart (cued four (cuePercept shown) (winPercept shown) false false) none 1) time =
        (((none : Option Bool), (⟨0, Nat.succ_pos 1⟩ : Fin (1 + 1))),
          (false, false, false, false)) ∨
      loop (visits (cued four (cuePercept shown) (winPercept shown) false false) none 1)
        (pupil four paid cue)
        (visitStart (cued four (cuePercept shown) (winPercept shown) false false) none 1) time =
        ((some true, (⟨1, Nat.lt_succ_self 1⟩ : Fin (1 + 1))), (true, false, false, false)) := by
  induction time with
  | zero => exact Or.inl rfl
  | succ time ih =>
    rcases ih with asking | told
    · exact Or.inr ((congrArg (interact _ _) asking).trans
        (pupil_ask four (cuePercept shown) (winPercept shown) paid cue (fun _ => rfl)
          false false false false false))
    · exact Or.inl ((congrArg (interact _ _) told).trans
        (pupil_tell four (cuePercept shown) (winPercept shown) paid cue (decide_eq_true rfl)
          (fun _ => decide_eq_false zero_ne_one) false false true false false false))

/-- **A witness of `StopsLearningAt`.** In the cued door whose door it holds from the start, the
pupil stops learning at once: the doors it holds never change. -/
theorem pupil_stops (four : 4 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    StopsLearningAt (pupil_keepsOnly four paid cue)
      (visits (cued four (cuePercept shown) (winPercept shown) false false) none 1)
      (visitStart (cued four (cuePercept shown) (winPercept shown) false false) none 1) 0 := by
  intro later _
  change (pupil_keepsOnly four paid cue).learned
      (loop (visits (cued four (cuePercept shown) (winPercept shown) false false) none 1)
        (pupil four paid cue)
        (visitStart (cued four (cuePercept shown) (winPercept shown) false false) none 1)
        later).2 = (false, false)
  rcases pupil_settled four shown later with asking | told
  · rw [asking]
    rfl
  · rw [told]
    rfl

/-- **A failing example of `StopsLearningAt`.** In the cued door whose door it does not hold, the
pupil has not stopped learning at the start: after its first miss it holds another door. -/
theorem pupil_goes_on (four : 4 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    ¬ StopsLearningAt (pupil_keepsOnly four paid cue)
      (visits (cued four (cuePercept shown) (winPercept shown) false true) none 1)
      (visitStart (cued four (cuePercept shown) (winPercept shown) false true) none 1) 0 := by
  intro stops
  have zero : loop (visits (cued four (cuePercept shown) (winPercept shown) false true) none 1)
      (pupil four paid cue)
      (visitStart (cued four (cuePercept shown) (winPercept shown) false true) none 1) 0 =
        (((none : Option Bool), ⟨0, Nat.succ_pos 1⟩), (false, false, false, false)) := rfl
  have one : loop (visits (cued four (cuePercept shown) (winPercept shown) false true) none 1)
      (pupil four paid cue)
      (visitStart (cued four (cuePercept shown) (winPercept shown) false true) none 1) 1 = _ :=
    (congrArg (interact _ _) zero).trans
      (pupil_ask four (cuePercept shown) (winPercept shown) paid cue (fun _ => rfl)
        false true false false false)
  have two : loop (visits (cued four (cuePercept shown) (winPercept shown) false true) none 1)
      (pupil four paid cue)
      (visitStart (cued four (cuePercept shown) (winPercept shown) false true) none 1) 2 = _ :=
    (congrArg (interact _ _) one).trans
      (pupil_tell four (cuePercept shown) (winPercept shown) paid cue (decide_eq_true rfl)
        (fun _ => decide_eq_false zero_ne_one) false true _ false false false)
  have held := stops 2 (Nat.zero_le 2)
  change (pupil_keepsOnly four paid cue).learned
      (loop (visits (cued four (cuePercept shown) (winPercept shown) false true) none 1)
        (pupil four paid cue)
        (visitStart (cued four (cuePercept shown) (winPercept shown) false true) none 1)
        2).2 = (false, false) at held
  rw [two] at held
  have bad : ((true, false) : Bool × Bool) = (false, false) := held
  cases bad

end AcornVerif.Kernel
