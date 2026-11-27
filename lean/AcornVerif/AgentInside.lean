import AcornVerif.CuedDoorsReward
import AcornVerif.StoredExperience

namespace AcornVerif.Kernel
open Acorn Acorn.Features

variable {interface : Interface} {Φ : Type}

def asChooser (agent : Agent interface) : Agent interface :=
  chooser (fun (_ : Unit) (choice : Act interface) => (choice, ())) agent.initial ()
    (fun memory percept => (agent.act memory percept).1)
    (fun memory percept _ => (agent.act memory percept).2)

theorem asChooser_driven (agent : Agent interface) (percepts : ℕ → Percept interface)
    (time : ℕ) : driven (asChooser agent) percepts time = (driven agent percepts time, ()) := by
  induction time with
  | zero => rfl
  | succ time ih =>
    change ((asChooser agent).act (driven (asChooser agent) percepts time) (percepts time)).2 = _
    rw [ih]
    rfl

theorem every_agent_chooses (agent : Agent interface) (world : World interface)
    (start : world.State) (time : ℕ) :
    actionAt world (asChooser agent) start time = actionAt world agent start time :=
  actionAt_of_response (fun percepts time => by
    change ((asChooser agent).act (driven (asChooser agent) percepts time) (percepts time)).1 = _
    rw [asChooser_driven]
    rfl) world start time

def Adapts (agent : Agent interface) : Prop :=
  ∃ (first second : ℕ → Percept interface) (time : ℕ), first time = second time ∧
    response agent first time ≠ response agent second time

theorem experienceFree_driven {agent : Agent interface} {advance : agent.Memory → agent.Memory}
    (law : ∀ memory percept, (agent.act memory percept).2 = advance memory)
    (percepts : ℕ → Percept interface) (time : ℕ) :
    driven agent percepts time = advanced advance agent.initial time := by
  induction time with
  | zero => rfl
  | succ time ih => exact (law _ _).trans (congrArg advance ih)

theorem ExperienceFree.not_adapts {agent : Agent interface} (free : ExperienceFree agent) :
    ¬ Adapts agent := by
  obtain ⟨advance, law⟩ := free
  rintro ⟨first, second, time, same, differ⟩
  apply differ
  change (agent.act (driven agent first time) (first time)).1 =
    (agent.act (driven agent second time) (second time)).1
  rw [experienceFree_driven law, experienceFree_driven law, same]

def echo (interface : Interface) (rule : Percept interface → Act interface)
    (first : Act interface) : Agent interface where
  Memory := Act interface
  initial := first
  act := fun held percept => (held, rule percept)

theorem echo_adapts (rule : Percept interface → Act interface) (first : Act interface)
    (here there : Percept interface) (differ : rule here ≠ rule there) :
    Adapts (echo interface rule first) :=
  ⟨fun time => if time = 0 then here else there, fun _ => there, 1, rfl, differ⟩

def ReadsObservation (feedback : Percept interface → Φ) (agent : Agent interface) : Prop :=
  ∃ (percepts : ℕ → Percept interface) (time : ℕ) (here there : Percept interface),
    feedback here = feedback there ∧
      (agent.act (driven agent percepts time) here).1 ≠
        (agent.act (driven agent percepts time) there).1

def LearnsAt (feedback : Percept interface → Φ) (agent : Agent interface) : Prop :=
  ∃ (first second : ℕ → Percept interface) (time : ℕ) (here there : Percept interface),
    feedback here = feedback there ∧
      (agent.act (driven agent first time) here).1 ≠
        (agent.act (driven agent second time) here).1 ∧
      (agent.act (driven agent second time) here).1 ≠
        (agent.act (driven agent second time) there).1

theorem LearnsAt.reads {feedback : Percept interface → Φ} {agent : Agent interface}
    (learns : LearnsAt feedback agent) : ReadsObservation feedback agent := by
  obtain ⟨-, second, time, here, there, same, -, differ⟩ := learns
  exact ⟨second, time, here, there, same, differ⟩

theorem Stepped.not_reads {feedback : Percept interface → Φ} {agent : Agent interface}
    (stepped : Stepped feedback agent) : ¬ ReadsObservation feedback agent := by
  obtain ⟨step, law⟩ := stepped
  rintro ⟨percepts, time, here, there, same, differ⟩
  apply differ
  rw [law, law, same]

theorem Stepped.not_learnsAt {feedback : Percept interface → Φ} {agent : Agent interface}
    (stepped : Stepped feedback agent) : ¬ LearnsAt feedback agent :=
  fun learns => stepped.not_reads learns.reads

theorem ExperienceFree.not_learnsAt {feedback : Percept interface → Φ} {agent : Agent interface}
    (free : ExperienceFree agent) : ¬ LearnsAt feedback agent := by
  obtain ⟨advance, law⟩ := free
  rintro ⟨first, second, time, here, there, -, differ, -⟩
  apply differ
  rw [experienceFree_driven law, experienceFree_driven law]

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

def twoBits (four : 4 ≤ interface.actions.word.toNat) (past sees : Percept interface → Bool) :
    Agent interface where
  Memory := Bool
  initial := false
  act := fun held percept => (key four held (sees percept), past percept)

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

def Recalls (agent : Agent interface) (lag : ℕ) : Prop :=
  ∃ decode : agent.Memory → Percept interface, ∀ (percepts : ℕ → Percept interface) (time : ℕ),
    decode (driven agent percepts (time + lag + 1)) = percepts time

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

theorem not_recalls_of_subsingleton (agent : Agent interface) [Subsingleton agent.Memory]
    (here there : Percept interface) (differ : here ≠ there) (lag : ℕ) : ¬ Recalls agent lag := by
  rintro ⟨decode, law⟩
  have first := law (fun _ => here) 0
  have second := law (fun _ => there) 0
  rw [Subsingleton.elim (driven agent (fun _ => here) (0 + lag + 1))
    (driven agent (fun _ => there) (0 + lag + 1))] at first
  exact differ (first.symm.trans second)

end AcornVerif.Kernel
