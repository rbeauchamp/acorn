import AcornVerif.CuedDoorsPupil

namespace AcornVerif.Kernel
open Acorn Acorn.Features

variable {interface : Interface}

def cueFrame (shown : Percept interface) (situation : Bool) : Frame interface :=
  { shown.frame with potentials := Vector.replicate _ situation, achieved := false }

def cuePercept (shown : Percept interface) (situation : Bool) : Percept interface :=
  ⟨cueFrame shown situation, ⟨0⟩⟩

def winPercept (shown : Percept interface) : Percept interface :=
  ⟨{ shown.frame with achieved := true }, ⟨1⟩⟩

def paid (percept : Percept interface) : Bool := decide (percept.reward = (⟨1⟩ : Binary32))

def cue (percept : Percept interface) : Bool :=
  percept.frame.potentials[0]'(by decide)

def rewardOnly (shown : Percept interface) (percept : Percept interface) : Percept interface :=
  ⟨cueFrame shown false, percept.reward⟩

theorem zero_ne_one : (⟨0⟩ : Binary32) ≠ ⟨1⟩ :=
  fun same => absurd (congrArg Binary32.bits same) (by decide)

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
      (fun same => absurd (congrArg cue same : false = true) Bool.false_ne_true)
      reference origin⟩

theorem cued_perceiving (four : 4 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    PerceivingDecides (fun percept : Percept interface => percept.reward)
      (visitRuns (cuedDoors four (cuePercept shown) (winPercept shown)) 1)
      (SeparatesBy (cuedDoors four (cuePercept shown) (winPercept shown))
        (cuedGoals four (cuePercept shown) (winPercept shown)) 1 3 cuedAll 2) :=
  ⟨(cuedNeeded (fun percept : Percept interface => percept.reward) four (cuePercept shown)
      (winPercept shown) (rewardOnly shown) (fun _ => rfl) (fun _ => rfl)).perceivingNeeded
      cuedAll, pupil four paid cue, (cued_reward four shown).2.2.1⟩

end AcornVerif.Kernel
