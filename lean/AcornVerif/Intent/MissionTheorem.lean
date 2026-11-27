import AcornVerif.Intent.BigClassConsequences
import AcornVerif.Intent.OneStream

namespace AcornVerif.Intent.MissionTheorem

open LeanIntent WorldInterface Postcondition BigClass OneStream

structure Rung extends Trial where
  updates : agent.Memory → Obs × Rat → List Update
  work : agent.Memory → Obs × Rat → Nat
  resume : agent.Memory → agent.Memory

def Rung.learner (r : Rung) (i : r.Index) : Learner :=
  OneStream.learner (r.member i).world r.agent r.updates r.work r.resume

structure Mission (r : Rung) : Prop where
  interface : ∀ i, worldInterface.Meets (couple (r.member i).world r.agent)
  big : bigClass.Meets r.toTrial
  stream : ∀ i, oneStream.Meets (r.learner i)
  achieves : postcondition.Meets r.toTrial

theorem Rung.interface_met (r : Rung) (i : r.Index) :
    worldInterface.Meets (couple (r.member i).world r.agent) :=
  couple_meets _ _ (fun _ _ _ => Iff.rfl) (fun _ _ _ => trivial)

theorem Mission.of_records {r : Rung} (big : bigClass.Meets r.toTrial)
    (stream : ∀ i, oneStream.Meets (r.learner i)) (achieves : postcondition.Meets r.toTrial) :
    Mission r :=
  ⟨r.interface_met, big, stream, achieves⟩

def MemoryBounded (r : Rung) : Prop :=
  ∃ L : List r.agent.Memory, ∀ i ins t s (m : r.agent.Memory),
    (r.learner i).Reaches ins t s m → m ∈ L

def WorkBounded (r : Rung) : Prop :=
  ∃ W : Nat, ∀ i ins t s m, (r.learner i).Takes ins t s m →
    (r.learner i).stepWork s m (ins t) ≤ W ∧ ((r.learner i).stepUpdates s m (ins t)).length ≤ W

def LearnsOnArrival (r : Rung) : Prop :=
  ∀ i, learnsOnArrival.holds (r.learner i)

def KeepsDiscipline (r : Rung) : Prop :=
  ∀ i, learnsEveryStep.holds (r.learner i) ∧ plansEveryStep.holds (r.learner i) ∧
    neverResetsItself.holds (r.learner i) ∧ resumesWhereStopped.holds (r.learner i)

theorem Rung.stream_met {r : Rung} (memory : MemoryBounded r) (work : WorkBounded r)
    (once : LearnsOnArrival r) (discipline : KeepsDiscipline r) :
    ∀ i, oneStream.Meets (r.learner i) := by
  obtain ⟨L, held⟩ := memory
  obtain ⟨W, spent⟩ := work
  exact fun i => oneStream_meets.mpr ⟨once i, ⟨W, spent i⟩, ⟨L, held i⟩, (discipline i).1,
    (discipline i).2.1, (discipline i).2.2.1, fun _ _ _ _ _ => rfl, (discipline i).2.2.2⟩

theorem six_memories : ∀ m : Option Bool × Bool, m ∈ ([(none, false), (none, true),
    (some false, false), (some false, true), (some true, false), (some true, true)] :
      List (Option Bool × Bool)) := by
  rintro ⟨_ | _ | _, _ | _⟩ <;> decide

theorem finder_finite : ∃ L : List finder.Memory, ∀ m, m ∈ L :=
  ⟨_, six_memories⟩

def doorsRung (total : List Rat → Rat) (pay : Rat) : Rung where
  toTrial := doors total pay finder
  updates := fun _ _ => [.learn (.stream 0), .other]
  work := fun _ _ => 2
  resume := id

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
