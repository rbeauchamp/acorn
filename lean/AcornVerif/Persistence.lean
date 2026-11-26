import AcornVerif.CurrentAccounting
import AcornVerif.CuedDoorsPupil
import Mathlib.Data.Fintype.Prod

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

structure KeepsOnly (agent : Agent interface) (Learned Named : Type)
    (law : Named → Learned → Percept interface → Named) where
  learned : agent.Memory → Learned
  named : agent.Memory → Named
  isSealed : Function.Injective (fun memory => (learned memory, named memory))
  lawful : ∀ memory percept,
    named (agent.act memory percept).2 = law (named memory) (learned memory) percept

def pupilLaw (sees : Percept interface → Bool) (named : Bool × Bool) (_ : Bool × Bool)
    (percept : Percept interface) : Bool × Bool :=
  match named with
  | (false, _) => (true, sees percept)
  | (true, seen) => (false, seen)

def pupil_keepsOnly (four : 4 ≤ interface.actions.word.toNat)
    (signal sees : Percept interface → Bool) :
    KeepsOnly (pupil four signal sees) (Bool × Bool) (Bool × Bool) (pupilLaw sees) where
  learned := fun (memory : Bool × Bool × Bool × Bool) => (memory.2.2.1, memory.2.2.2)
  named := fun (memory : Bool × Bool × Bool × Bool) => (memory.1, memory.2.1)
  isSealed := by
    rintro ⟨phase, seen, first, second⟩ ⟨phase', seen', first', second'⟩ same
    have parts := Prod.mk.inj same
    have doors := Prod.mk.inj parts.1
    have clocks := Prod.mk.inj parts.2
    rw [show phase = phase' from clocks.1, show seen = seen' from clocks.2,
      show first = first' from doors.1, show second = second' from doors.2]
  lawful := by
    rintro ⟨phase, seen, first, second⟩ percept
    cases phase <;> rfl

theorem not_keepsOnly_of_card {agent : Agent interface} {Learned Named : Type}
    [Fintype agent.Memory] [Fintype Learned] [Fintype Named]
    (more : Fintype.card Learned * Fintype.card Named < Fintype.card agent.Memory)
    (law : Named → Learned → Percept interface → Named) :
    IsEmpty (KeepsOnly agent Learned Named law) :=
  ⟨fun keeps => by
    have fits := Fintype.card_le_of_injective _ keeps.isSealed
    rw [Fintype.card_prod] at fits
    exact absurd more (Nat.not_lt.mpr fits)⟩

theorem pupil_not_keepsOnly (four : 4 ≤ interface.actions.word.toNat)
    (signal sees : Percept interface → Bool)
    (law : Bool → Bool × Bool → Percept interface → Bool) :
    IsEmpty (KeepsOnly (pupil four signal sees) (Bool × Bool) Bool law) := by
  have more : Fintype.card (Bool × Bool) * Fintype.card Bool <
      Fintype.card (Bool × Bool × Bool × Bool) := by decide
  exact @not_keepsOnly_of_card interface (pupil four signal sees) (Bool × Bool) Bool
    (inferInstanceAs (Fintype (Bool × Bool × Bool × Bool))) _ _ more law

theorem not_sealed_beside {Memory Record Learned Named : Type} (learned : Memory → Learned)
    (named : Memory → Named) (memory : Memory) (first second : Record) (differ : first ≠ second) :
    ¬ Function.Injective
      (fun pair : Memory × Record => (learned pair.1, named pair.1)) :=
  fun injective => differ (congrArg Prod.snd
    (injective (a₁ := (memory, first)) (a₂ := (memory, second)) rfl))

theorem no_room_beside {Memory Record State : Type} [Fintype Memory] [Fintype Record]
    [Fintype State] [Nonempty Memory] (full : Fintype.card State ≤ Fintype.card Memory)
    (two : 2 ≤ Fintype.card Record) (view : Memory × Record → State) :
    ¬ Function.Injective view := by
  intro injective
  have fits := Fintype.card_le_of_injective view injective
  rw [Fintype.card_prod] at fits
  have twice : Fintype.card Memory * 2 ≤ Fintype.card Memory * Fintype.card Record :=
    Nat.mul_le_mul_left _ two
  have positive : 0 < Fintype.card Memory := Fintype.card_pos
  omega

def StopsLearningAt {agent : Agent interface} {Learned Named : Type}
    {law : Named → Learned → Percept interface → Named} (keeps : KeepsOnly agent Learned Named law)
    (world : World interface) (start : world.State) (time : ℕ) : Prop :=
  ∀ later, time ≤ later →
    keeps.learned (memoryAt world agent start later) =
      keeps.learned (memoryAt world agent start time)

def declaresNothing (agent : Agent interface) :
    KeepsOnly agent Unit agent.Memory (fun memory _ percept => (agent.act memory percept).2) where
  learned := fun _ => ()
  named := fun memory => memory
  isSealed := fun _ _ same => congrArg Prod.snd same
  lawful := fun _ _ => rfl

theorem nothing_stops (agent : Agent interface) (world : World interface) (start : world.State)
    (time : ℕ) : StopsLearningAt (declaresNothing agent) world start time :=
  fun _ _ => rfl

end AcornVerif.Kernel

namespace AcornVerif.Persistence
open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

theorem control_sealed : Function.Injective
    (fun agent : Agent interface profile config criterion dimension planning => agent.control) := by
  rintro ⟨control, aligned, episodes⟩ ⟨other, aligned', episodes'⟩ same
  have equal : control = other := same
  subst equal
  rfl

structure Recorder (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (planning : PlanningSelection) where
  learner : Agent interface profile config criterion dimension planning
  route : List ℕ

theorem recorder_unsealed
    (agent : Agent interface profile config criterion dimension planning) :
    ¬ Function.Injective
      (fun recorder : Recorder interface profile config criterion dimension planning =>
        recorder.learner.control) := by
  intro injective
  have same := injective (a₁ := ⟨agent, []⟩) (a₂ := ⟨agent, [0]⟩) rfl
  have routes := congrArg Recorder.route same
  cases routes

end AcornVerif.Persistence
