/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.WorldInterface

/-!
# Intent record: the invariants of learning from one stream

Contract 3 of Acorn's mission contract (`docs/mission-contract.md`, section "Contract 3: invariants
of learning from one stream") opens with six plain sentences that the owner confirmed on 2026-11-03
as the statement of how Acorn's agent learns from its one stream of experience. That restatement is
this record's only source. The agents that work on Acorn wrote it from a research report on the
research of Rich Sutton, Khurram Javed and Oak Lab, and the owner adopted it by confirming it; the
owners' log keeps whose words they are (`AcornVerif.Intent.Decisions.ownersLog`). The record's
writer had read contract 1's record, `AcornVerif.Intent.WorldInterface.worldInterface`, the mission
contract, whose design sections describe the executing agent's checkpoints and learners, rbeauchamp/acorn#215
and rbeauchamp/acorn#90, and passages of the design document `docs/design.md` on the agent's step
orders, before writing it, and none of the executing agent's code; the record imports nothing of
Acorn's but contract 1's record module.

The subject, `Learner`, refines contract 1's subject, `AcornVerif.Intent.WorldInterface.System`
(one world, one agent and the run that couples them), only as far as the six sentences need to speak
of what the agent keeps and does. It adds three things the agent reports of itself: the internal
updates its step makes from a memory on the experience it is given (`updates`), each one of the
closed kinds `Update` names, with the training datum of each learning update (`Datum`); the work of
that step (`work`); and the memory it resumes with after a stop (`resume`). The record reads the
memory the agent holds, and the memory a run keeps for it, from contract 1's fields, and the rest
from these three. That the three describe what the agent actually does is trusted, as contract 1
trusts that a world's and an agent's fields are theirs: an agent that replays a stored experience
and reports a planning update, resets its memory and reports another kind of update, or reports less
work than it does, is a subject that meets the record. Where a planning update with a learned model
ends and a replay of stored experience begins is the line obligation 7 of the mission contract
draws, and proving that Acorn's executing agent reports truthfully is the fifth step of
rbeauchamp/acorn#215.

The eight properties are the record's reading of the six sentences, each over every step a run takes
under every sequence of outside inputs, or every memory a run holds or every stop it makes, with no
domain hypothesis: sentence 6 is carried by those quantifiers and by having no exception. Each
property's plain words were written from the finished predicate and are trusted, not proved; the
consequences, and the choices decided on the owner's behalf, are recorded with their reasons in the
record's confirmation file, `lean/AcornVerif/Intent/OneStream.md`. What the owner confirmed is the six
sentences; that this record carries them is the agents' judgment, and the owners' log attaches the
owner's answer to this record's revision on that judgment.
-/

namespace AcornVerif.Intent.OneStream

open LeanIntent WorldInterface

/-- What a learning update takes as its training datum: an experience of the agent's own stream,
by how many steps before the update's own step the stream gave it, or anything else. -/
inductive Datum where
  /-- The experience the agent's own stream gave it `age` steps before the step that makes the update:
  `stream 0` is the experience that step was given. The experience is what the run gives the agent at
  a step, the observation and the reward, and a learning update that takes it may use, beside it,
  short-term credit-assignment memory such as an eligibility trace, and the agent's learned state. -/
  | stream (age : Nat)
  /-- A training datum that is no experience of the agent's own stream, such as another stream's
  experience or data handed to the agent from outside its stream. -/
  | other
  deriving DecidableEq

/-- The kind of one internal update the agent's step makes. -/
inductive Update where
  /-- A learning update, whose training datum is `datum`. -/
  | learn (datum : Datum)
  /-- A planning update with a model the agent has learned, which takes no training datum. -/
  | plan
  /-- A reset: an update that discards what some or all of the agent's memory holds and sets that part
  back to its value at the start of the agent's life, as an episodic agent's memory is reset when an
  episode ends. -/
  | reset
  /-- Any other internal update, such as one of an eligibility trace: it takes no training datum,
  plans with no model and resets nothing. -/
  | other
  deriving DecidableEq

/-- One world, one agent and the run that couples them (contract 1's `System`), with what the agent
reports of itself: the internal updates its step makes, the work of its step, and the memory it
resumes with after a stop. -/
structure Learner extends WorldInterface.System where
  /-- The internal updates the agent's step makes, in order, from a memory on the experience it is
  given there. -/
  updates : Memory → Obs × Rat → List Update
  /-- The work the agent's step does from a memory on the experience it is given there, in a unit of
  cost the subject fixes. -/
  work : Memory → Obs × Rat → Nat
  /-- The memory the agent resumes with after a stop at which it held the given memory. -/
  resume : Memory → Memory

namespace Learner

variable (w : Learner)

/-- The internal updates of the agent's step at the state `s`, the memory `m` and the input `e`:
those its step makes from `m` on the experience the run gives it there. -/
def stepUpdates (s : w.State) (m : w.Memory) (e : w.Input) : List Update :=
  w.updates m (w.given s m e)

/-- The work of the agent's step at the state `s`, the memory `m` and the input `e`. -/
def stepWork (s : w.State) (m : w.Memory) (e : w.Input) : Nat :=
  w.work m (w.given s m e)

/-- `w.Stops ins t s m`: under the outside inputs `ins`, the run reaches the state `s` and the memory
`m` after `t` steps and takes no step from them. -/
def Stops (ins : Nat → w.Input) (t : Nat) (s : w.State) (m : w.Memory) : Prop :=
  w.Reaches ins t s m ∧ w.goesOn s m (ins t) = false

end Learner

/-! ## The properties -/

/-- At every step a run takes, under every sequence of outside inputs, every learning update the
agent's step makes takes as its training datum the experience its own stream gave it at that step. -/
def learnsOnArrival : Clause Learner :=
  ⟨"each step, every learning update learns from the experience that step was given", fun w =>
    ∀ ins t s m, w.Takes ins t s m →
      ∀ d, Update.learn d ∈ w.stepUpdates s m (ins t) → d = .stream 0⟩

/-- There is one number such that, at every step a run takes, under every sequence of outside inputs,
the work of the agent's step and the number of its internal updates are at most that number. -/
def boundedWork : Clause Learner :=
  ⟨"the work of each step, and the number of its internal updates, stay within one bound", fun w =>
    ∃ W : Nat, ∀ ins t s m, w.Takes ins t s m →
      w.stepWork s m (ins t) ≤ W ∧ (w.stepUpdates s m (ins t)).length ≤ W⟩

/-- There is one finite list of memories such that, at every time of every run, under every sequence
of outside inputs, the memory the agent holds is in that list. -/
def boundedMemory : Clause Learner :=
  ⟨"the agent holds one of finitely many memories at every time of every run", fun w =>
    ∃ L : List w.Memory, ∀ ins t s m, w.Reaches ins t s m → m ∈ L⟩

/-- If the agent's step makes a learning update at some step some run takes, then at every step every
run takes, under every sequence of outside inputs, its step makes a learning update. -/
def learnsEveryStep : Clause Learner :=
  ⟨"an agent that learns on some step learns on every step", fun w =>
    (∃ ins t s m d, w.Takes ins t s m ∧ Update.learn d ∈ w.stepUpdates s m (ins t)) →
      ∀ ins t s m, w.Takes ins t s m → ∃ d, Update.learn d ∈ w.stepUpdates s m (ins t)⟩

/-- If the agent's step makes a planning update at some step some run takes, then at every step every
run takes, under every sequence of outside inputs, its step makes a planning update. -/
def plansEveryStep : Clause Learner :=
  ⟨"an agent that plans on some step plans on every step", fun w =>
    (∃ ins t s m, w.Takes ins t s m ∧ Update.plan ∈ w.stepUpdates s m (ins t)) →
      ∀ ins t s m, w.Takes ins t s m → Update.plan ∈ w.stepUpdates s m (ins t)⟩

/-- At every step a run takes, under every sequence of outside inputs, the agent's step makes no
reset. -/
def neverResetsItself : Clause Learner :=
  ⟨"no step of the agent resets its memory", fun w =>
    ∀ ins t s m, w.Takes ins t s m → Update.reset ∉ w.stepUpdates s m (ins t)⟩

/-- At every step a run takes, under every sequence of outside inputs, the agent begins the next step
with the memory its own answer produced. -/
def keepsItsMemory : Clause Learner :=
  ⟨"each step, the agent keeps the memory its own answer produced", fun w =>
    ∀ ins t s m, w.Takes ins t s m →
      w.kept s m (ins t) (w.answer s m (ins t)).2 = (w.answer s m (ins t)).2⟩

/-- At every time at which a run stops, under every sequence of outside inputs, the memory the agent
resumes with is the memory it held there. -/
def resumesWhereStopped : Clause Learner :=
  ⟨"after every stop, the agent resumes with the memory it held when it stopped", fun w =>
    ∀ ins t s m, w.Stops ins t s m → w.resume m = m⟩

/-- A configuration of a run: a learner, its outside inputs, a time, a state and a memory. -/
abbrev Configuration : Type 1 :=
  (w : Learner) × (Nat → w.Input) × Nat × w.State × w.Memory

/-- The intent record of the invariants of learning from one stream. -/
def oneStream : IntentRecord Learner where
  shape := .value _
  dom := []
  props := [learnsOnArrival, boundedWork, boundedMemory, learnsEveryStep, plansEveryStep,
    neverResetsItself, keepsItsMemory, resumesWhereStopped]
  vocab := [
    ⟨"the run takes a step", Configuration,
      fun c => c.1.Takes c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2⟩,
    ⟨"the run stops", Configuration, fun c => c.1.Stops c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2⟩]

/-- A learner meets the record exactly when each of the eight properties holds of it. -/
theorem oneStream_meets {w : Learner} :
    oneStream.Meets w ↔
      learnsOnArrival.holds w ∧ boundedWork.holds w ∧ boundedMemory.holds w ∧
        learnsEveryStep.holds w ∧ plansEveryStep.holds w ∧ neverResetsItself.holds w ∧
          keepsItsMemory.holds w ∧ resumesWhereStopped.holds w := by
  constructor
  · intro hm
    have h := hm.2
    exact ⟨h _ (by simp [oneStream]), h _ (by simp [oneStream]), h _ (by simp [oneStream]),
      h _ (by simp [oneStream]), h _ (by simp [oneStream]), h _ (by simp [oneStream]),
      h _ (by simp [oneStream]), h _ (by simp [oneStream])⟩
  · intro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [oneStream, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8

/-! ## Learners run faithfully -/

/-- The learner of the world `W` and the agent `A`, run as contract 1's faithful run `couple` runs
them, with the agent's reports: the internal updates `ups`, the work `cost` and the resumption
`back`. -/
def learner (W : World) (A : Agent W.Obs W.Act) (ups : A.Memory → W.Obs × Rat → List Update)
    (cost : A.Memory → W.Obs × Rat → Nat) (back : A.Memory → A.Memory) : Learner :=
  { toSystem := couple W A, updates := ups, work := cost, resume := back }

/-- A learner run faithfully meets the record when the agent has finitely many memories, every
learning update it reports learns from the experience its step was given, its work and number of
updates are bounded, it reports a learning update on every experience or on none and a planning
update on every experience or on none, it reports no reset, and it resumes with the memory it
held. -/
theorem learner_meets (W : World) (A : Agent W.Obs W.Act)
    (ups : A.Memory → W.Obs × Rat → List Update) (cost : A.Memory → W.Obs × Rat → Nat)
    (back : A.Memory → A.Memory)
    (hlearn : ∀ m o d, Update.learn d ∈ ups m o → d = .stream 0)
    (hcost : ∃ B, ∀ m o, cost m o ≤ B ∧ (ups m o).length ≤ B)
    (hfin : ∃ L : List A.Memory, ∀ m, m ∈ L)
    (hevery : (∀ m o, ∃ d, Update.learn d ∈ ups m o) ∨ ∀ m o d, Update.learn d ∉ ups m o)
    (hplan : (∀ m o, Update.plan ∈ ups m o) ∨ ∀ m o, Update.plan ∉ ups m o)
    (hreset : ∀ m o, Update.reset ∉ ups m o) (hback : ∀ m, back m = m) :
    oneStream.Meets (learner W A ups cost back) := by
  obtain ⟨B, hB⟩ := hcost
  obtain ⟨L, hL⟩ := hfin
  refine oneStream_meets.mpr ⟨fun _ _ _ _ _ d hd => hlearn _ _ d hd,
    ⟨B, fun _ _ _ _ _ => hB _ _⟩, ⟨L, fun _ _ _ m _ => hL m⟩, ?_, ?_,
    fun _ _ _ _ _ => hreset _ _, fun _ _ _ _ _ => rfl, fun _ _ _ m _ => hback m⟩
  · rcases hevery with h | h
    · exact fun _ _ _ _ _ _ => h _ _
    · exact fun ⟨_, _, _, _, d, _, hd⟩ => absurd hd (h _ _ d)
  · rcases hplan with h | h
    · exact fun _ _ _ _ _ _ => h _ _
    · exact fun ⟨_, _, _, _, _, hd⟩ => absurd hd (h _ _)

/-- An agent that answers with what it sees and remembers only the last thing it saw. -/
def lastSeen : Agent Bool Bool where
  Memory := Bool
  initial := false
  act _ o := (o.1, o.1)

/-- The faithful run of contract 1's `mirror` and `lastSeen`, in which the agent reports one learning
update on the experience each step was given, one unit of work, and resumes with the memory it held:
each refuting learner below changes one part of it. -/
def base : Learner :=
  learner mirror lastSeen (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id

/-- Every memory of `lastSeen` is in the list of its two memories. -/
theorem lastSeen_finite : ∃ L : List lastSeen.Memory, ∀ m, m ∈ L :=
  ⟨[false, true], fun m => by cases m with
    | false => exact .head _
    | true => exact .tail _ (.head _)⟩

theorem base_meets : oneStream.Meets base :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨1, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩ lastSeen_finite
    (.inl fun _ _ => ⟨_, List.mem_singleton_self _⟩)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- The outside inputs that ask the run to stop at every step. -/
def stopAtOnce : Nat → Bool := fun _ => true

/-- O2: the record has no domain hypothesis, `base` takes its first step, and it stops before its
first step when asked to: an instance of each predicate of its vocabulary. -/
theorem oneStream_o2 : O2 oneStream := by
  refine (o2_correct _).mpr ⟨⟨base, fun _ h => nomatch h⟩, fun p hp => ?_⟩
  simp only [oneStream, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨base, neverStop, 0, false, false⟩, takes_first (w := base.toSystem) rfl⟩
  · exact ⟨⟨base, stopAtOnce, 0, false, false⟩, .start, rfl⟩

/-- O2 before running: `base` meets the whole record. -/
theorem oneStream_o2Run : O2Run oneStream :=
  (o2Run_correct _).mpr ⟨base, base_meets.1, base_meets.2⟩

/-! ## Learners that fail one property each -/

/-- `base` with a learning update that learns from the experience the previous step was given. -/
def replaysPrevious : Learner := { base with updates := fun _ _ => [.learn (.stream 1)] }

/-- A world whose state counts the steps taken and which shows that count. -/
def clock : World where
  State := Nat
  Obs := Nat
  Act := Bool
  start := 0
  observe s := s
  reward _ := 0
  available _ _ := True
  step s _ := s + 1

/-- An agent that always answers `true` and keeps nothing. -/
def still : Agent Nat Bool := always true

/-- The faithful run of `clock` and `still`, whose step reports as much work as the count it is
shown, and no update. -/
def growingWork : Learner := learner clock still (fun _ _ => []) (fun _ o => o.1) id

/-- The run of `clock` and `still` is at the count `t` after `t` steps. -/
theorem clock_reaches : ∀ t, (couple clock still).Reaches neverStop t t ()
  | 0 => .start
  | t + 1 => .next (clock_reaches t) rfl

/-- The faithful run of `mirror` and contract 1's `echo`, which counts its steps, reporting one
learning update on each experience and one unit of work. -/
def counting : Learner :=
  learner mirror echo (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 1) id

/-- The run of `mirror` and `echo` holds the memory `t` after `t` steps. -/
theorem echo_counts : ∀ t, ∃ s, (couple mirror echo).Reaches neverStop t s t
  | 0 => ⟨_, .start⟩
  | t + 1 =>
    let ⟨_, h⟩ := echo_counts t
    ⟨_, .next h rfl⟩

/-- Each member of a list of naturals is at most its sum. -/
theorem le_sum_of_mem : ∀ {L : List Nat} {n : Nat}, n ∈ L → n ≤ L.sum
  | _ :: _, _, .head _ => by simp only [List.sum_cons]; omega
  | a :: _, _, .tail _ h => by have := le_sum_of_mem h; simp only [List.sum_cons]; omega

/-- No list of naturals holds every natural. -/
theorem exists_not_mem (L : List Nat) : ∃ n, n ∉ L :=
  ⟨L.sum + 1, fun h => absurd (le_sum_of_mem h) (by omega)⟩

/-- An agent that answers with what it sees and remembers whether it has taken a step. -/
def trained : Agent Bool Bool where
  Memory := Bool
  initial := false
  act _ o := (o.1, true)

/-- The faithful run of `mirror` and `trained`, which reports a learning update on its first step
only. -/
def learnsOnce : Learner :=
  learner mirror trained (fun m _ => cond m [] [.learn (.stream 0)]) (fun _ _ => 1) id

/-- The faithful run of `mirror` and `trained`, which reports a planning update on its first step
only. -/
def plansOnce : Learner := learner mirror trained (fun m _ => cond m [] [.plan]) (fun _ _ => 1) id

/-- The run of `mirror` and `trained` has taken a step after one step. -/
theorem trained_reaches_one : (couple mirror trained).Reaches neverStop 1 false true :=
  .next .start rfl

/-- `base` with a reset after its learning update. -/
def resetsItself : Learner := { base with updates := fun _ _ => [.learn (.stream 0), .reset] }

/-- `base` run so that the agent begins each step with the other memory than its answer produced. -/
def runFlipsMemory : Learner := { base with kept := fun _ _ _ m => cond m false true }

/-- `base` resuming with the other memory than the one it held. -/
def resumesOther : Learner := { base with resume := fun m => cond m false true }

/-- O3: each property fails of a learner that differs from `base`, or from a learner run faithfully,
where it attacks. -/
theorem oneStream_o3 : O3 oneStream := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [oneStream, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨replaysPrevious, fun h => absurd (h neverStop 0 _ _ (takes_first (w := base.toSystem) rfl)
      _ (List.mem_singleton_self _)) (by decide)⟩
  · refine ⟨growingWork, fun ⟨B, hB⟩ => ?_⟩
    have := (hB neverStop (B + 1) _ _ ⟨clock_reaches (B + 1), rfl⟩).1
    exact absurd this (by change ¬ B + 1 ≤ B; omega)
  · refine ⟨counting, fun ⟨L, hL⟩ => ?_⟩
    obtain ⟨n, hn⟩ := exists_not_mem L
    obtain ⟨_, hr⟩ := echo_counts n
    exact hn (hL neverStop n _ _ hr)
  · refine ⟨learnsOnce, fun h => ?_⟩
    obtain ⟨d, hd⟩ := h ⟨neverStop, 0, false, false, _, takes_first (w := learnsOnce.toSystem) rfl,
      List.mem_singleton_self _⟩ neverStop 1 false true ⟨trained_reaches_one, rfl⟩
    exact nomatch hd
  · refine ⟨plansOnce, fun h => ?_⟩
    have hd := h ⟨neverStop, 0, false, false, takes_first (w := plansOnce.toSystem) rfl,
      List.mem_singleton_self _⟩ neverStop 1 false true ⟨trained_reaches_one, rfl⟩
    exact nomatch hd
  · exact ⟨resetsItself, fun h => h neverStop 0 _ _ (takes_first (w := base.toSystem) rfl)
      (.tail _ (.head _))⟩
  · exact ⟨runFlipsMemory, fun h => Bool.noConfusion
      (h neverStop 0 _ _ (takes_first (w := runFlipsMemory.toSystem) rfl))⟩
  · exact ⟨resumesOther, fun h => Bool.noConfusion (h stopAtOnce 0 _ _ ⟨.start, rfl⟩)⟩

/-- O4: the subject is declared a plain value, of which O4 asks nothing. Why that shape is chosen is
recorded in the record's confirmation file. -/
theorem oneStream_o4 : O4 oneStream := (o4_correct _).mpr trivial

/-- O5 with the widest freedom, which every record meets. -/
theorem oneStream_o5_widest : O5 oneStream .widest := o5_widest _

/-- `base` reporting two units of work at each step: a second model of the record. -/
def baseWorkTwo : Learner :=
  learner mirror lastSeen (fun _ _ => [.learn (.stream 0)]) (fun _ _ => 2) id

theorem baseWorkTwo_meets : oneStream.Meets baseWorkTwo :=
  learner_meets _ _ _ _ _ (fun _ _ _ h => Update.learn.inj (List.mem_singleton.mp h))
    ⟨2, fun _ _ => ⟨Nat.le_refl _, by decide⟩⟩ lastSeen_finite
    (.inl fun _ _ => ⟨_, List.mem_singleton_self _⟩)
    (.inr fun _ _ h => nomatch List.mem_singleton.mp h)
    (fun _ _ h => nomatch List.mem_singleton.mp h) fun _ => rfl

/-- O5 does not hold with equality: `base` and `baseWorkTwo` both meet the record and differ. -/
theorem oneStream_not_o5_eq : ¬ O5 oneStream .eq := by
  refine not_o5_eq base_meets baseWorkTwo_meets fun h => ?_
  have hw : ∀ e : baseWorkTwo.Input, baseWorkTwo.stepWork baseWorkTwo.start baseWorkTwo.initial e = 1 :=
    h ▸ fun _ => rfl
  exact absurd (hw false) (by decide)

/-- The pair obligation of each property's pair whose only input is trivial, in the class of every
subject: `base` fulfils each property. -/
theorem oneStream_pairs :
    ∀ c ∈ oneStream.props, OPair (Pair.whole oneStream c) (fun _ => True) :=
  fun c hc => (oPair_whole_iff _ _ _).mpr ⟨base, trivial, fun _ => base_meets.2 c hc⟩

/-- **Every world can be served.** For every world, an agent exists whose faithful run with it meets
the record: the agent that always answers with one action, keeps nothing, reports no update and no
work, and resumes with the memory it held. -/
theorem every_world_served (W : World) (a₀ : W.Act) :
    ∃ A : Agent W.Obs W.Act, ∃ ups cost back, oneStream.Meets (learner W A ups cost back) :=
  ⟨always a₀, fun _ _ => [], fun _ _ => 0, id,
    learner_meets _ _ _ _ _ (fun _ _ _ h => nomatch h) ⟨0, fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _⟩⟩
      ⟨[()], fun _ => .head _⟩ (.inr fun _ _ _ h => nomatch h) (.inr fun _ _ h => nomatch h)
      (fun _ _ h => nomatch h) fun _ => rfl⟩

end AcornVerif.Intent.OneStream
