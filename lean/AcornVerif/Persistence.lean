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

* `KeepsOnly`: an agent keeps only what is declared. Its memory is determined by a part declared
  as what it has learned and a named part, and the named part follows a stated law of the two
  parts and the percept. Only the learned part is written freely. The declaration is the mission
  contract's, for each agent of the ladder, and never the agent's choice.
* `declaresNothing`, `nothing_stops`: why the choice cannot be the agent's. With nothing declared
  as learned and its whole memory named, every agent keeps only what is declared and has stopped
  learning from the start.
* `pupil_keepsOnly`: a witness. The pupil's two doors are what it has learned; its clock bit and
  the situation it last read are named, with their law. It is an agent whose learned part comes to
  hold what was rewarded.
* `not_keepsOnly_of_card`, `pupil_not_keepsOnly`: the failing example. An agent whose memory takes
  more values than the declared parts can hold keeps more than is declared, under every law; the
  pupil, declared as its two doors and its clock bit alone, is one, since its memory also holds
  the situation it last read.
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

/-- **The agent keeps only what is declared.** Its memory is determined by the part declared as
what it has learned and a named part; and the named part after a decision is a stated law of the
two parts before it and the percept. What the agent writes freely is its learned part alone.

The declaration is a parameter here and the structure does not fix it. `docs/mission-contract.md`
declares what an agent has learned, for each agent of its ladder; the agent never chooses it. Left
to the agent, the declaration would be empty: with nothing declared as learned, every agent meets
this structure (`declaresNothing`). No such declaration is made yet for any agent of the ladder
(obligations 19 and 22 of that document).

Its witness is `pupil_keepsOnly`. Its failing example is `not_keepsOnly_of_card`, with
`pupil_not_keepsOnly` as an instance: an agent whose memory holds a record the declared parts
cannot hold meets this structure at those parts under no law. -/
structure KeepsOnly (agent : Agent interface) (Learned Named : Type)
    (law : Named → Learned → Percept interface → Named) where
  /-- The part of the memory declared as what the agent has learned. -/
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

/-- **An agent whose memory holds more than the declared parts can hold keeps more than is
declared.** Where the learned part and the named part together take fewer values than the agent's
memory, no declaration of those parts is a `KeepsOnly`, whatever the law: two memories would have
the same declared parts, so something persists beside them. -/
theorem not_keepsOnly_of_card {agent : Agent interface} {Learned Named : Type}
    [Fintype agent.Memory] [Fintype Learned] [Fintype Named]
    (more : Fintype.card Learned * Fintype.card Named < Fintype.card agent.Memory)
    (law : Named → Learned → Percept interface → Named) :
    IsEmpty (KeepsOnly agent Learned Named law) :=
  ⟨fun keeps => by
    have fits := Fintype.card_le_of_injective _ keeps.isSealed
    rw [Fintype.card_prod] at fits
    exact absurd more (Nat.not_lt.mpr fits)⟩

/-- **The pupil, declared as its two doors and its clock bit alone, keeps more than is declared.**
Its memory also holds the situation it last read, a record those parts cannot hold, so no law of
a named clock bit makes that declaration a `KeepsOnly`. -/
theorem pupil_not_keepsOnly (four : 4 ≤ interface.actions.word.toNat)
    (signal sees : Percept interface → Bool)
    (law : Bool → Bool × Bool → Percept interface → Bool) :
    IsEmpty (KeepsOnly (pupil four signal sees) (Bool × Bool) Bool law) := by
  have more : Fintype.card (Bool × Bool) * Fintype.card Bool <
      Fintype.card (Bool × Bool × Bool × Bool) := by decide
  exact @not_keepsOnly_of_card interface (pupil four signal sees) (Bool × Bool) Bool
    (inferInstanceAs (Fintype (Bool × Bool × Bool × Bool))) _ _ more law

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
memory declared as learned does not change. Its witness is `pupil_stops` and its failing example
`pupil_goes_on`.

This does not yet define the agents a learner is compared with. With nothing declared as learned
every agent has stopped from the start (`nothing_stops`), so the declaration has to be the mission
contract's and not the agent's; and an agent that stops only at the horizon before which reward is
counted earns before it what it would have earned had it gone on, so the time a comparator stops
has to be stated relative to that horizon. Both are open (obligations 19 and 22 of
`docs/mission-contract.md`). -/
def StopsLearningAt {agent : Agent interface} {Learned Named : Type}
    {law : Named → Learned → Percept interface → Named} (keeps : KeepsOnly agent Learned Named law)
    (world : World interface) (start : world.State) (time : ℕ) : Prop :=
  ∀ later, time ≤ later →
    keeps.learned (memoryAt world agent start later) =
      keeps.learned (memoryAt world agent start time)

/-- **With nothing declared as learned, every agent keeps only what is declared.** The learned
part is empty, the whole memory is named, and the named part's law is the agent's own update. -/
def declaresNothing (agent : Agent interface) :
    KeepsOnly agent Unit agent.Memory (fun memory _ percept => (agent.act memory percept).2) where
  learned := fun _ => ()
  named := fun memory => memory
  isSealed := fun _ _ same => congrArg Prod.snd same
  lawful := fun _ _ => rfl

/-- **With nothing declared as learned, every agent has stopped learning from the start**, in
every world, with the memory, the actions and the rewards it has under any other declaration. So
the agents that stop learning are a class of agents only once the declaration is fixed for each
agent by something other than the agent. -/
theorem nothing_stops (agent : Agent interface) (world : World interface) (start : world.State)
    (time : ℕ) : StopsLearningAt (declaresNothing agent) world start time :=
  fun _ _ => rfl

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
