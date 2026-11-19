/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentAccounting
import AcornVerif.CuedDoorsPupil
import Mathlib.Data.Fintype.Prod

/-!
# What may persist from one decision to the next

* `KeepsOnly`: an agent keeps only what it declares. Its memory is determined by a part it
  declares as what it has learned and a part it names, and the named part follows a stated law of
  the two parts and the percept. Only the learned part is written freely.
* `pupil_keepsOnly`: a witness. The pupil's two doors are what it has learned; its clock bit and
  the situation it last read are named, with their law. It is an agent whose learned part comes to
  hold what was rewarded.
* `not_sealed_beside`: a recorder beside a learner, declared as the learner is, is not sealed: two
  memories that differ only in the record have the same declared parts.
* `no_room_beside`: where the learner's declared parts already take every value its memory can,
  no declaration at all seals a recorder beside it: there is no room for the record.
* `control_sealed`: the executed agent's state is determined by its `control`, so with
  `actOrdered_learners` on `main` nothing that a decision reads persists outside
  `learners agent.control`. `recorder_unsealed`: an executed agent with a route kept in a field of
  its own beside `control` is not determined by its `control`.
-/

namespace AcornVerif.Kernel
open Acorn.Features

variable {interface : Interface}

/-- **The agent keeps only what it declares.** Its memory is determined by the part it declares
as learned and the part it names; and the named part after a decision is a stated law of the two
parts before it and the percept. What the agent writes freely is its learned part alone. -/
structure KeepsOnly (agent : Agent interface) (Learned Named : Type)
    (law : Named → Learned → Percept interface → Named) where
  /-- The part of the memory the agent declares as what it has learned. -/
  learned : agent.Memory → Learned
  /-- The part of the memory the clause names: clocks, generators, traces and the like. -/
  named : agent.Memory → Named
  /-- Nothing else persists: the two parts determine the memory. -/
  isSealed : Function.Injective (fun memory => (learned memory, named memory))
  /-- The named part follows its law. -/
  lawful : ∀ memory percept,
    named (agent.act memory percept).2 = law (named memory) (learned memory) percept

/-- The law of the pupil's named part: its clock bit alternates, and at a visit's start it reads
the situation. -/
def pupilLaw (sees : Percept interface → Bool) (named : Bool × Bool) (_ : Bool × Bool)
    (percept : Percept interface) : Bool × Bool :=
  match named with
  | (false, _) => (true, sees percept)
  | (true, seen) => (false, seen)

/-- **A witness: the pupil keeps only its two doors**, beside a clock bit and the situation it
last read. Its learned part comes to hold the door that was rewarded in each situation. -/
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

/-- **A recorder beside a learner is not sealed.** Declared as the learner is, two memories that
differ only in the record have the same learned and named parts. -/
theorem not_sealed_beside {Memory Record Learned Named : Type} (learned : Memory → Learned)
    (named : Memory → Named) (memory : Memory) (first second : Record) (differ : first ≠ second) :
    ¬ Function.Injective
      (fun pair : Memory × Record => (learned pair.1, named pair.1)) :=
  fun injective => differ (congrArg Prod.snd
    (injective (a₁ := (memory, first)) (a₂ := (memory, second)) rfl))

/-- **Where the learner uses every state its declaration allows, no declaration seals a recorder
beside it.** If the declared parts have no more values than the learner's memory, a memory with a
record of two or more values beside it maps into them by no injective map. -/
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

/-- **The agent stops learning at a time**, in its run in a world: from then on the part of its
memory it declares as learned does not change. A definition only: no witness and no failing
example of it is built here. -/
def StopsLearningAt {agent : Agent interface} {Learned Named : Type}
    {law : Named → Learned → Percept interface → Named} (keeps : KeepsOnly agent Learned Named law)
    (world : World interface) (start : world.State) (time : ℕ) : Prop :=
  ∀ later, time ≤ later →
    keeps.learned (memoryAt world agent start later) =
      keeps.learned (memoryAt world agent start time)

end AcornVerif.Kernel

namespace AcornVerif.Persistence
open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- **The executed agent's state is its `control`.** Two agents with one `control` are one
agent: its other two fields are proofs about `control`. -/
theorem control_sealed : Function.Injective
    (fun agent : Agent interface profile config criterion dimension planning => agent.control) := by
  rintro ⟨control, aligned, episodes⟩ ⟨other, aligned', episodes'⟩ same
  have equal : control = other := same
  subst equal
  rfl

/-- An executed agent with a record of its own beside its state: the shape of a recorder beside
the learner. -/
structure Recorder (interface : Interface) (profile : FeatureProfile) (config : Features.Config)
    (criterion : Criterion) (dimension : Dimension) (planning : PlanningSelection) where
  /-- The learner. -/
  learner : Agent interface profile config criterion dimension planning
  /-- A stored route, as action indices. -/
  route : List ℕ

/-- **A recorder beside the executed learner is not determined by the learner's `control`.** -/
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
