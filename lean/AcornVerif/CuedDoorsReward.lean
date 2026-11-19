/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CuedDoorsPupil

/-!
# The cued doors over every interface with four actions and one percept

The hypotheses of `cued_summary` about percepts are met from any one percept of the interface:
the two situations' percepts are that percept's frame with the achievement flag off and on, both
with the reward word zero, and the winning percept carries the reward word one. With the reward
word as the feedback, `cued_reward` is then a statement with no hypothesis but four actions and a
percept: no agent driven by its reward words separates, every experience-free agent solves at
most two members, the pupil separates and retains, and no one reference world conceals the class's
goals in the full percept.
-/

namespace AcornVerif.Kernel
open Acorn Acorn.Features

variable {interface : Interface}

/-- A frame with its achievement flag set to a situation. -/
def cueFrame (shown : Percept interface) (situation : Bool) : Frame interface :=
  { shown.frame with achieved := situation }

/-- The percept of a situation: the frame that shows it, with the reward word zero. -/
def cuePercept (shown : Percept interface) (situation : Bool) : Percept interface :=
  ⟨cueFrame shown situation, ⟨0⟩⟩

/-- The winning percept: the reward word one. -/
def winPercept (shown : Percept interface) : Percept interface := ⟨shown.frame, ⟨1⟩⟩

/-- Whether a percept's reward word is one. -/
def paid (percept : Percept interface) : Bool := decide (percept.reward = (⟨1⟩ : Binary32))

/-- The situation a percept's frame shows. -/
def cue (percept : Percept interface) : Bool := percept.frame.achieved

/-- The projection that keeps a percept's reward word and nothing of its frame. -/
def rewardOnly (shown : Percept interface) (percept : Percept interface) : Percept interface :=
  ⟨cueFrame shown false, percept.reward⟩

/-- The reward word zero is not the reward word one. -/
theorem zero_ne_one : (⟨0⟩ : Binary32) ≠ ⟨1⟩ :=
  fun same => absurd (congrArg Binary32.bits same) (by decide)

/-- **The cued doors, with the reward word as the feedback.** Over every interface with four
actions and a percept: no agent whose actions depend on its clock and its reward words alone
solves more than three of the four members on one of its first two visits; every experience-free
agent solves at most two on any visit; the pupil solves all four on its second visit and retains
them before visit 3 with no lapse; and no reference world conceals the class's goals in the full
percept, so the class is outside contract 2 (b) as `Conceals` states it. -/
theorem cued_reward (four : 4 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    (∀ agent : Agent interface,
      FeedbackDriven (fun percept : Percept interface => percept.reward) agent → ∀ counted,
        ¬ SeparatesBy (cuedDoors four (cuePercept shown) (winPercept shown))
          (cuedGoals four (cuePercept shown) (winPercept shown)) 1 3 counted 2 agent) ∧
    (∀ agent : Agent interface, ExperienceFree agent → ∀ (visit : ℕ)
      (solved : Finset (Bool × Bool)),
      (∀ index ∈ solved, SolvesOnVisit (cuedDoors four (cuePercept shown) (winPercept shown))
        (cuedGoals four (cuePercept shown) (winPercept shown)) 1 agent visit index) →
          solved.card ≤ 2) ∧
    SeparatesBy (cuedDoors four (cuePercept shown) (winPercept shown))
      (cuedGoals four (cuePercept shown) (winPercept shown)) 1 3 cuedAll 2
      (pupil four paid cue) ∧
    RetainsBut (cuedDoors four (cuePercept shown) (winPercept shown))
      (cuedGoals four (cuePercept shown) (winPercept shown)) 1 3 0 (pupil four paid cue) ∧
    ∀ (reference : World interface) (origin : reference.State),
      ¬ Conceals (cuedDoors four (cuePercept shown) (winPercept shown))
        (cuedGoals four (cuePercept shown) (winPercept shown)) reference origin := by
  obtain ⟨blind, frozen, separates, retains⟩ :=
    cued_summary (fun percept : Percept interface => percept.reward) four (cuePercept shown)
      (winPercept shown) (rewardOnly shown) (fun _ => rfl) (fun _ => rfl) paid cue
      (decide_eq_true rfl) (fun _ => decide_eq_false zero_ne_one) (fun _ => rfl)
  exact ⟨blind, frozen, separates, retains, fun reference origin =>
    cued_reveals four (cuePercept shown) (winPercept shown)
      (fun same => absurd
        (congrArg (fun percept : Percept interface => percept.frame.achieved) same)
        Bool.false_ne_true) reference origin⟩

/-- **The cued doors need perceiving, and a learner meets them.** With the reward word as the
feedback: no agent that acts as a clock-and-reward agent on everything the class shows it
separates at the bound 3 before visit 2, and the pupil does. -/
theorem cued_perceiving (four : 4 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    PerceivingNeeded (fun percept : Percept interface => percept.reward)
        (visitRuns (cuedDoors four (cuePercept shown) (winPercept shown)) 1)
        (SeparatesBy (cuedDoors four (cuePercept shown) (winPercept shown))
          (cuedGoals four (cuePercept shown) (winPercept shown)) 1 3 cuedAll 2) ∧
      SeparatesBy (cuedDoors four (cuePercept shown) (winPercept shown))
        (cuedGoals four (cuePercept shown) (winPercept shown)) 1 3 cuedAll 2
        (pupil four paid cue) :=
  ⟨(cuedNeeded (fun percept : Percept interface => percept.reward) four (cuePercept shown)
      (winPercept shown) (rewardOnly shown) (fun _ => rfl) (fun _ => rfl)).perceivingNeeded
      cuedAll, (cued_reward four shown).2.2.1⟩

end AcornVerif.Kernel
