/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.BigClassConsequences
import AcornVerif.Intent.OneStream

/-!
# The mission theorem's statement for one class of worlds

The mission contract (`docs/mission-contract.md`, section "The mission theorem and its ladder") asks
for one theorem for each class of a ladder of classes: that Acorn's agent achieves goals over that
class. Its four contracts each have an intent record. This module puts the four records together
into the one proposition such a theorem proves, `Mission`, so that the way the theorem depends on
its contracts is checked by Lean and not argued in prose.

The subject, `Rung`, is one class of the ladder as the records read it: a class of worlds with the
agent that learns in it (`AcornVerif.Intent.Postcondition.Trial`, the subject of the records of
contract 2 and of the postcondition), and what that agent reports of its own steps (the internal
updates, the work and the resumption that the record of contract 3 reads). `Mission` holds of a rung
when

* the faithful run of the agent in every member meets contract 1's record
  (`AcornVerif.Intent.WorldInterface.worldInterface`);
* the class with the agent meets contract 2's record (`AcornVerif.Intent.BigClass.bigClass`);
* the faithful run of the agent in every member, with the agent's reports, meets contract 3's
  record (`AcornVerif.Intent.OneStream.oneStream`);
* the class with the agent meets the postcondition's record
  (`AcornVerif.Intent.Postcondition.postcondition`).

The runs the four records read are one run: the run in a member that the records of contract 2 and
of the postcondition compute with is contract 1's faithful run, never stopped
(`AcornVerif.Intent.Postcondition.run_reaches`), and contract 3's learner is that run with the
agent's reports (`Rung.learner`). A rung's run is faithful by how it is built, so the first clause
holds of every rung (`Rung.interface_met`); it is stated so that the proposition names all four
contracts.

`doors_mission` shows the four records can be met together: the two-door class with the agent
`finder` meets `Mission`, for every fair aggregation and payment. It is a model of the statement,
not a result about Acorn's agent or about a class of the ladder.

What the proposition does not say:

* It speaks of one agent, whose runs are determined. How the fraction of failing runs of an agent
  that explores with random draws enters, under fork F4 of the mission contract, is stated where the
  proposition is applied to a family of agents, not here.
* The reports are the agent's own. That they describe what its step does is a separate proof for
  each agent; for Acorn's executing agent it is the fifth step of rbeauchamp/acorn#215.
* Two of the four records, those of contract 2 and of the postcondition, have not had their blind
  second reading or their confirmation file (rbeauchamp/acorn#214, rbeauchamp/acorn#219), so the
  proposition can change with them.
-/

namespace AcornVerif.Intent.MissionTheorem

open LeanIntent WorldInterface Postcondition BigClass OneStream

/-- One class of the mission's ladder, as the four records read it: a class of worlds with the agent
that learns in it, and what that agent reports of its own steps. -/
structure Rung extends Trial where
  /-- The internal updates the agent's step makes, in order, from a memory on the experience it is
  given there. -/
  updates : agent.Memory → Obs × Rat → List Update
  /-- The work the agent's step does from a memory on the experience it is given there, in a unit of
  cost the rung fixes. -/
  work : agent.Memory → Obs × Rat → Nat
  /-- The memory the agent resumes with after a stop at which it held the given memory. -/
  resume : agent.Memory → agent.Memory

/-- The agent of a rung as contract 3's learner in the member `i`: contract 1's faithful run of the
member's world and the agent, with the agent's reports. -/
def Rung.learner (r : Rung) (i : r.Index) : Learner :=
  OneStream.learner (r.member i).world r.agent r.updates r.work r.resume

/-- **The mission theorem's statement for one class of the ladder.** The agent of the rung achieves
goals over its class: its run in every member meets contract 1, the class is big as contract 2 says,
its run in every member keeps the invariants of contract 3, and the postcondition holds of the class
and the agent. -/
structure Mission (r : Rung) : Prop where
  /-- Contract 1: the interface every world meets, in the agent's run in each member. -/
  interface : ∀ i, worldInterface.Meets (couple (r.member i).world r.agent)
  /-- Contract 2: what makes the class big. -/
  big : bigClass.Meets r.toTrial
  /-- Contract 3: the invariants of learning from one stream, in the agent's run in each member. -/
  stream : ∀ i, oneStream.Meets (r.learner i)
  /-- The postcondition: what achieving goals promises. -/
  achieves : postcondition.Meets r.toTrial

/-- The run of a rung's agent in each member meets contract 1's record, by how the run is built: it
is the faithful run, and a member makes every action available at every state. -/
theorem Rung.interface_met (r : Rung) (i : r.Index) :
    worldInterface.Meets (couple (r.member i).world r.agent) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) (fun _ _ _ => trivial)

/-- The mission's statement holds of a rung whose class meets the records of contract 2 and of the
postcondition and whose agent's runs meet the record of contract 3. -/
theorem Mission.of_records {r : Rung} (big : bigClass.Meets r.toTrial)
    (stream : ∀ i, oneStream.Meets (r.learner i)) (achieves : postcondition.Meets r.toTrial) :
    Mission r :=
  ⟨r.interface_met, big, stream, achieves⟩

/-! ## Contract 3 as named premises

The record of contract 3 holds of an agent's run only through what the agent reports of its own
steps. For an agent whose reports are not yet proved, its clauses are the premises below. Each names
the open obligation of `docs/mission-contract.md` it states and the issue that owns it. -/

/-- **Obligation 6, a bound on reachable memory** (rbeauchamp/acorn#195). In every member, the
agent holds one of finitely many memories at every time of every run. -/
def MemoryBounded (r : Rung) : Prop :=
  ∀ i, boundedMemory.holds (r.learner i)

/-- **Obligation 7, executed work** (rbeauchamp/acorn#90). In every member, the work of each step of
the agent, and the number of its internal updates, stay within one bound. -/
def WorkBounded (r : Rung) : Prop :=
  ∀ i, boundedWork.holds (r.learner i)

/-- **Obligation 7, learning from each experience once** (rbeauchamp/acorn#233). In every member,
every learning update of every step learns from the experience that step was given. -/
def LearnsOnce (r : Rung) : Prop :=
  ∀ i, learnsOnArrival.holds (r.learner i)

/-- **The rest of contract 3 that a faithful run does not give** (the fifth step of
rbeauchamp/acorn#215). In every member: an agent that learns on some step learns on every step, one
that plans on some step plans on every step, no step makes a reset, and after every stop the agent
resumes with the memory it held. -/
def KeepsDiscipline (r : Rung) : Prop :=
  ∀ i, learnsEveryStep.holds (r.learner i) ∧ plansEveryStep.holds (r.learner i) ∧
    neverResetsItself.holds (r.learner i) ∧ resumesWhereStopped.holds (r.learner i)

/-- The four premises give contract 3's record in every member. The remaining property, that the
agent keeps the memory its own answer produced, holds of every rung by how its run is built. -/
theorem Rung.stream_met {r : Rung} (memory : MemoryBounded r) (work : WorkBounded r)
    (once : LearnsOnce r) (discipline : KeepsDiscipline r) :
    ∀ i, oneStream.Meets (r.learner i) :=
  fun i => oneStream_meets.mpr ⟨once i, work i, memory i, (discipline i).1, (discipline i).2.1,
    (discipline i).2.2.1, fun _ _ _ _ _ => rfl, (discipline i).2.2.2⟩

/-! ## The four records can be met together -/

/-- Every pair of a door the agent may know and a door it last tried is in the list of the six. -/
theorem six_memories : ∀ m : Option Bool × Bool, m ∈ ([(none, false), (none, true),
    (some false, false), (some false, true), (some true, false), (some true, true)] :
      List (Option Bool × Bool)) := by
  rintro ⟨_ | _ | _, _ | _⟩ <;> decide

/-- Every memory of `finder` is in the list of its six memories. -/
theorem finder_finite : ∃ L : List finder.Memory, ∀ m, m ∈ L :=
  ⟨_, six_memories⟩

/-- The two-door class with the agent `finder`, which reports, at every step, one learning update on
the experience the step was given, one other update for the door it remembers having tried, and two
units of work, and which resumes with the memory it held. -/
def doorsRung (total : List Rat → Rat) (pay : Rat) : Rung where
  toTrial := doors total pay finder
  updates := fun _ _ => [.learn (.stream 0), .other]
  work := fun _ _ => 2
  resume := id

/-- **The four records are jointly satisfiable.** The two-door class with the agent `finder` meets
the mission's statement, for every fair aggregation and payment. -/
theorem doors_mission (total : List Rat → Rat) (pay : Rat) (h : Fair total pay) :
    Mission (doorsRung total pay) :=
  Mission.of_records (doors_big total pay finder)
    (fun _ => learner_meets _ _ _ _ _
      (fun _ _ d hd => by
        rcases List.mem_cons.mp hd with h1 | h2
        · exact Update.learn.inj h1
        · exact nomatch List.mem_singleton.mp h2)
      ⟨2, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ finder_finite
      (.inl fun _ _ => ⟨_, List.mem_cons_self⟩)
      (.inr fun _ _ hp => by
        rcases List.mem_cons.mp hp with h1 | h2
        · exact nomatch h1
        · exact nomatch List.mem_singleton.mp h2)
      (fun _ _ hr => by
        rcases List.mem_cons.mp hr with h1 | h2
        · exact nomatch h1
        · exact nomatch List.mem_singleton.mp h2)
      fun _ => rfl)
    (doors_finder_meets total pay h)

end AcornVerif.Intent.MissionTheorem
