/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CuedDoorsReward
import AcornVerif.StoredExperience

/-!
# Words about the agent's inside, at the kernel's level

Proposed definitions, each read through an agent's responses to sequences of percepts, with what
each keeps out and a witness, and one word the kernel cannot carry.

* *values*: `every_agent_chooses`. Every agent is, action for action, an agent that selects from
  a preference it forms from its memory and its percept. So "its action comes from its values"
  says nothing of a kernel agent until what the values are is fixed by the agent's own code.
* *learned*: `Adapts`, the action depends on earlier percepts. `ExperienceFree.not_adapts` keeps
  out every agent that keeps nothing; `echo_adapts` is a witness.
* *at what it perceives*: `ReadsObservation`, the action depends on the percept beyond the
  feedback; `LearnsAt`, on one percept the action changed with experience, and after that
  experience it depends on the percept beyond the feedback. It is the conjunction of those two
  dependences and does not say that experience changed how the percept is read. `Stepped.not_reads`
  and `Stepped.not_learnsAt` keep out every agent stepped by the feedback,
  `ExperienceFree.not_learnsAt` every agent that keeps nothing; `pupil_learnsAt` is a witness, and
  `twoBits_learnsAt` an agent it admits that carries one independent bit for each dependence.
* *stores*: `Recalls`, the memory determines the percept received a number of steps earlier.
  `historian_recalls` is a witness at every lag; `not_recalls_of_subsingleton` a failing example.
-/

namespace AcornVerif.Kernel
open Acorn Acorn.Features

variable {interface : Interface} {Φ : Type}

/-! ## Values -/

/-- The chooser that selects whatever its preference names, with the agent's action as the
preference and the agent's memory as its core. -/
def asChooser (agent : Agent interface) : Agent interface :=
  chooser (fun (_ : Unit) (choice : Act interface) => (choice, ())) agent.initial ()
    (fun memory percept => (agent.act memory percept).1)
    (fun memory percept _ => (agent.act memory percept).2)

/-- The chooser's core is the agent's memory. -/
theorem asChooser_driven (agent : Agent interface) (percepts : ℕ → Percept interface)
    (time : ℕ) : driven (asChooser agent) percepts time = (driven agent percepts time, ()) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    change ((asChooser agent).act (driven (asChooser agent) percepts time) (percepts time)).2 = _
    rw [ih]
    rfl

/-- **Every agent chooses by a preference.** The chooser built from an agent takes the agent's
action at every time in every world. -/
theorem every_agent_chooses (agent : Agent interface) (world : World interface)
    (start : world.State) (time : ℕ) :
    actionAt world (asChooser agent) start time = actionAt world agent start time :=
  actionAt_of_response (fun percepts time => by
    change ((asChooser agent).act (driven (asChooser agent) percepts time) (percepts time)).1 = _
    rw [asChooser_driven]
    rfl) world start time

/-! ## Learned -/

/-- **The agent adapts.** On two sequences of percepts that end in one percept, it takes different
actions on that percept: what it perceived earlier changed what it does. -/
def Adapts (agent : Agent interface) : Prop :=
  ∃ (first second : ℕ → Percept interface) (time : ℕ), first time = second time ∧
    response agent first time ≠ response agent second time

/-- An experience-free agent's memory does not depend on its percepts. -/
theorem experienceFree_driven {agent : Agent interface} {advance : agent.Memory → agent.Memory}
    (law : ∀ memory percept, (agent.act memory percept).2 = advance memory)
    (percepts : ℕ → Percept interface) (time : ℕ) :
    driven agent percepts time = advanced advance agent.initial time := by
  induction time with
  | zero => rfl
  | succ time ih => exact (law _ _).trans (congrArg advance ih)

/-- **An agent that keeps nothing does not adapt.** -/
theorem ExperienceFree.not_adapts {agent : Agent interface} (free : ExperienceFree agent) :
    ¬ Adapts agent := by
  obtain ⟨advance, law⟩ := free
  rintro ⟨first, second, time, same, differ⟩
  apply differ
  change (agent.act (driven agent first time) (first time)).1 =
    (agent.act (driven agent second time) (second time)).1
  rw [experienceFree_driven law, experienceFree_driven law, same]

/-- An agent that takes at each step the action a rule read from its previous percept. -/
def echo (interface : Interface) (rule : Percept interface → Act interface)
    (first : Act interface) : Agent interface where
  Memory := Act interface
  initial := first
  act := fun held percept => (held, rule percept)

/-- **A witness that adapts**: the echo of a rule that tells two percepts apart. -/
theorem echo_adapts (rule : Percept interface → Act interface) (first : Act interface)
    (here there : Percept interface) (differ : rule here ≠ rule there) :
    Adapts (echo interface rule first) :=
  ⟨fun time => if time = 0 then here else there, fun _ => there, 1, rfl, differ⟩

/-! ## At what it perceives -/

/-- **The agent reads its observation.** After some experience, on two percepts with one feedback
it takes different actions. -/
def ReadsObservation (feedback : Percept interface → Φ) (agent : Agent interface) : Prop :=
  ∃ (percepts : ℕ → Percept interface) (time : ℕ) (here there : Percept interface),
    feedback here = feedback there ∧
      (agent.act (driven agent percepts time) here).1 ≠
        (agent.act (driven agent percepts time) there).1

/-- **The agent has learned at what it perceives.** On one percept its action differs after two
experiences, and after the second it takes a different action on another percept with the same
feedback. This is the conjunction of two dependences of the action, on the past and on the present
percept beyond the feedback. It does not say that the second came from the first: an agent whose
action carries one independent bit for each, a reading of its previous percept and a fixed reading
of its present one, meets it (`twoBits_learnsAt`), though no experience changes how that agent
reads a percept. What dependence of the learned change on the percept should mean is not
defined. -/
def LearnsAt (feedback : Percept interface → Φ) (agent : Agent interface) : Prop :=
  ∃ (first second : ℕ → Percept interface) (time : ℕ) (here there : Percept interface),
    feedback here = feedback there ∧
      (agent.act (driven agent first time) here).1 ≠
        (agent.act (driven agent second time) here).1 ∧
      (agent.act (driven agent second time) here).1 ≠
        (agent.act (driven agent second time) there).1

/-- An agent that has learned at what it perceives reads its observation. -/
theorem LearnsAt.reads {feedback : Percept interface → Φ} {agent : Agent interface}
    (learns : LearnsAt feedback agent) : ReadsObservation feedback agent := by
  obtain ⟨-, second, time, here, there, same, -, differ⟩ := learns
  exact ⟨second, time, here, there, same, differ⟩

/-- **An agent stepped by the feedback does not read its observation.** -/
theorem Stepped.not_reads {feedback : Percept interface → Φ} {agent : Agent interface}
    (stepped : Stepped feedback agent) : ¬ ReadsObservation feedback agent := by
  obtain ⟨step, law⟩ := stepped
  rintro ⟨percepts, time, here, there, same, differ⟩
  apply differ
  rw [law, law, same]

/-- An agent stepped by the feedback has not learned at what it perceives. -/
theorem Stepped.not_learnsAt {feedback : Percept interface → Φ} {agent : Agent interface}
    (stepped : Stepped feedback agent) : ¬ LearnsAt feedback agent :=
  fun learns => stepped.not_reads learns.reads

/-- **An agent that keeps nothing has not learned at what it perceives.** -/
theorem ExperienceFree.not_learnsAt {feedback : Percept interface → Φ} {agent : Agent interface}
    (free : ExperienceFree agent) : ¬ LearnsAt feedback agent := by
  obtain ⟨advance, law⟩ := free
  rintro ⟨first, second, time, here, there, -, differ, -⟩
  apply differ
  rw [experienceFree_driven law, experienceFree_driven law]

/-- **A witness that has learned at what it perceives**: the pupil, with the reward word as the
feedback, over any interface with four actions and a percept. After a miss in the first situation
it tries another door there than after a success, and it tries a different key in the second
situation. -/
theorem pupil_learnsAt (four : 4 ≤ interface.actions.word.toNat) (shown : Percept interface) :
    LearnsAt (fun percept : Percept interface => percept.reward) (pupil four paid cue) := by
  refine ⟨fun time => if time = 1 then winPercept shown else cuePercept shown false,
    fun _ => cuePercept shown false, 2, cuePercept shown false, cuePercept shown true, rfl, ?_, ?_⟩
  · change key four false false ≠ key four false true
    intro same
    have apart := (key_inj four (congrArg Fin.val same)).2
    exact absurd apart (by decide)
  · change key four false true ≠ key four true false
    intro same
    have apart := (key_inj four (congrArg Fin.val same)).1
    exact absurd apart (by decide)

/-- An agent whose action carries two independent bits: a reading of the percept it received a
step earlier, which is all its memory, and a fixed reading of its present percept. -/
def twoBits (four : 4 ≤ interface.actions.word.toNat) (past sees : Percept interface → Bool) :
    Agent interface where
  Memory := Bool
  initial := false
  act := fun held percept => (key four held (sees percept), past percept)

/-- **An agent `LearnsAt` admits, though experience never changes how it reads a percept.** Where
the reading of the past tells two percepts apart, and the reading of the present tells apart two
percepts with one feedback, the agent of two independent bits has learned at what it perceives by
the definition: each of the two dependences holds, by a different bit. -/
theorem twoBits_learnsAt (four : 4 ≤ interface.actions.word.toNat)
    (feedback : Percept interface → Φ) (past sees : Percept interface → Bool)
    {one other here there : Percept interface} (earlier : past one ≠ past other)
    (same : feedback here = feedback there) (apart : sees here ≠ sees there) :
    LearnsAt feedback (twoBits four past sees) := by
  refine ⟨fun _ => one, fun _ => other, 1, here, there, same, ?_, ?_⟩
  · change key four (past one) (sees here) ≠ key four (past other) (sees here)
    exact fun equal => earlier (key_inj four (congrArg Fin.val equal)).1
  · change key four (past other) (sees here) ≠ key four (past other) (sees there)
    exact fun equal => apart (key_inj four (congrArg Fin.val equal)).2

/-! ## Stores -/

/-- **The agent recalls.** Its memory determines the percept it received `lag` steps before the
latest one, on every sequence of percepts: that percept is stored. -/
def Recalls (agent : Agent interface) (lag : ℕ) : Prop :=
  ∃ decode : agent.Memory → Percept interface, ∀ (percepts : ℕ → Percept interface) (time : ℕ),
    decode (driven agent percepts (time + lag + 1)) = percepts time

/-- **The historian recalls at every lag.** -/
theorem historian_recalls (agent : Agent interface) (shown : Percept interface) (lag : ℕ) :
    Recalls (historian agent) lag := by
  refine ⟨fun record => record.getD lag shown, fun percepts => ?_⟩
  induction lag with
  | zero => exact fun time => rfl
  | succ lag ih =>
    intro time
    change (percepts (time + lag + 1) :: driven (historian agent) percepts (time + lag + 1)).getD
      (lag + 1) shown = percepts time
    exact ih time

/-- **An agent with one memory recalls nothing**, where two percepts differ. -/
theorem not_recalls_of_subsingleton (agent : Agent interface) [Subsingleton agent.Memory]
    (here there : Percept interface) (differ : here ≠ there) (lag : ℕ) : ¬ Recalls agent lag := by
  rintro ⟨decode, law⟩
  have first := law (fun _ => here) 0
  have second := law (fun _ => there) 0
  rw [Subsingleton.elim (driven agent (fun _ => here) (0 + lag + 1))
    (driven agent (fun _ => there) (0 + lag + 1))] at first
  exact differ (first.symm.trans second)

end AcornVerif.Kernel
