/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.Postcondition

/-!
# Intent record: what makes a class of worlds big

Contract 2 of Acorn's mission contract (`docs/mission-contract.md`, section "Contract 2: what makes
a class of worlds big") opens with seven plain sentences that the owner confirmed on 2026-11-03 as
the statement of what makes a class of worlds big; the fourth lists four conditions, (a) to (d).
The owner confirmed the restatement as a whole, and the choices in it marked as Acorn's were decided
on the owner's behalf. That restatement is this record's only source. The agents that work on Acorn
wrote it from a research report on the research of Rich Sutton, Khurram Javed and Oak Lab, and the
owner adopted it by confirming it.

The record's writer had read, before writing it, everything the writer of the postcondition's record
lists in `AcornVerif.Intent.Postcondition`, and that record, whose writer it also is. In particular
it had read the design section the mission contract puts below this restatement, which gives Acorn's
precise forms of the four conditions over the kernel's definitions, and the design document's
sections on concealed goals and visits. So this record is not written blind to the forms the
kernel's proofs use, and the method's premise is weakened that far. Of the modules that define the
kernel's worlds, classes and visits the writer had read the first line of three declarations, and no
more; of the executing agent's code, nothing. The record imports nothing of Acorn's but the
postcondition's record module, and through it contract 1's.

The subject is the postcondition's, `AcornVerif.Intent.Postcondition.Trial`: a class of worlds with
the agent that learns in it. Sentence 2 says that bigness belongs to the pair of a world and an
agent, and the two records then speak of one thing, so that this record's properties can be the
preconditions under which the postcondition is asked. The five properties read the class only, not
its agent or how it aggregates reward (`reads_class`, in the module of this record's consequences).
Every quantity they read is computed by the postcondition's faithful run of an agent in a member.

The five properties are the record's reading of sentences 4 and 6:

* `goalsReachable` is condition (a): from the state in which any attempt of any agent's run in a
  member starts, some actions, fewer than an attempt's steps, lead to a state that meets the
  member's goal. It asks nothing of the states an agent's own actions lead to within an attempt, so
  it does not rule out traps.
* `goalsConcealed` is condition (b): there is one reference world such that, in every agent's run in
  a member, until a state first meets the member's goal the member gives the agent what the
  reference world gives it.
* `frozenShareSmall` is condition (c): some number smaller than the count of the counted members
  bounds how many of them an agent that keeps nothing of its experience solves on any attempt.
* `successShows` is the first half of sentence 6: one reading of what a member gives an agent says,
  at every time of every run, whether the member's goal is met then.
* `attemptsRecur` is the second half of sentence 6, with "coherent enough over time" read as: each
  member poses the same problem on every attempt, every attempt starting from the state the
  member's world starts in.

Condition (d) is not a property of this record. It speaks of how many separate problems the agent's
memory can hold solutions to at once, and in this subject each compared agent runs alone in each
member, so it never holds two members' solutions at once. Condition (d) needs a subject that
presents several members in one stream, which obligations 5, 6 and 10 of the mission contract own;
sentence 5 says that (d) is the target for larger classes. Sentences 1 to 3 give the reasons for the
conditions, and sentences 5 and 7 say how the classes are chosen; none adds a property. The record
has no domain hypothesis.

Decided on the owner's behalf in writing it, each to be checked against the second, blind
formalization and recorded in the record's confirmation file:

* Condition (d) is left to a subject with several members in one stream, as above.
* "Where its attempt starts", in condition (a), is the state in which an attempt starts in any
  agent's run, not one fixed state.
* Condition (b) is stated with one reference world that every member looks like, in observation and
  in reward, until its goal is first met.
* "Only a small share", in condition (c), asks that the share is never the whole of the counted
  members. How small the share is, is the margin between the bound and their count.
* "Success must show" is one reading of the observation and the reward that serves every member and
  is not told which member it reads.
* "Coherent enough over time" is the recurrence above. A class of worlds with no restarts would need
  another reading.

Each property's plain words were written from the finished predicate and are trusted, not proved.
What the owner confirmed is the seven sentences; that this record carries them is the agents'
judgment.
-/

namespace AcornVerif.Intent.BigClass

open LeanIntent WorldInterface Postcondition

/-- The state the member `M`'s world is in after the actions `acts`, taken in order from the state
`s`. -/
def afterActions {Obs Act : Type} (M : Member Obs Act) (s : M.State) (acts : List Act) : M.State :=
  acts.foldl M.step s

/-- What the member `M` gives the agent `A` at the time `t` of its run in it: the observation and
the reward of the state its world is in. -/
def given {Obs Act : Type} (M : Member Obs Act) (A : Agent Obs Act) (t : Nat) : Obs × Rat :=
  (M.observe (M.run A t).1, M.reward (M.run A t).1)

/-! ## The properties -/

/-- Condition (a): from the state in which any attempt of any agent's run in a member starts, some
actions, fewer than an attempt's steps, lead to a state that meets the member's goal. -/
def goalsReachable : Clause Trial :=
  ⟨"every member's goal can be reached within an attempt from the state the attempt starts in",
    fun w =>
    ∀ (A : Agent w.Obs w.Act) (i : w.Index) (n : Nat),
      ∃ acts : List w.Act, acts.length < w.length ∧
        (w.member i).goal
          (afterActions (w.member i) (w.stateAt A i (w.length * n)) acts) = true⟩

/-- Condition (b): there is one reference world such that, in every agent's run in a member, at
every time up to which no state has met the member's goal, the member gives the agent what the
reference world gives it at that time of its run there. -/
def goalsConcealed : Clause Trial :=
  ⟨"until a member's goal is first met, the member gives every agent what one reference world \
    gives it", fun w =>
    ∃ R : Member w.Obs w.Act, ∀ (A : Agent w.Obs w.Act) (i : w.Index) (t : Nat),
      (∀ u, u ≤ t → (w.member i).goal (w.stateAt A i u) = false) →
        given (w.member i) A t = given R A t⟩

/-- Condition (c): some number smaller than the count of the counted members bounds how many of
them an agent that keeps nothing of its experience solves on any attempt. -/
def frozenShareSmall : Clause Trial :=
  ⟨"on every attempt, an agent that keeps nothing of its experience solves at most a number of \
    the counted members that is smaller than their count", fun w =>
    ∃ k, k < w.counted.length ∧
      ∀ B : Agent w.Obs w.Act, KeepsNothing B → ∀ n, w.solvedCount B n ≤ k⟩

/-- The first half of sentence 6: one reading of what a member gives an agent says, at every time
of every agent's run in every member, whether the state then meets the member's goal. -/
def successShows : Clause Trial :=
  ⟨"one reading of what a member gives an agent says, at every time, whether the member's goal \
    is met then", fun w =>
    ∃ signal : w.Obs × Rat → Bool, ∀ (A : Agent w.Obs w.Act) (i : w.Index) (t : Nat),
      signal (given (w.member i) A t) = (w.member i).goal (w.stateAt A i t)⟩

/-- The second half of sentence 6: every attempt of every agent's run in a member starts from the
state the member's world starts in. -/
def attemptsRecur : Clause Trial :=
  ⟨"every attempt of every agent's run in a member starts from the state the member's world \
    starts in", fun w =>
    ∀ (A : Agent w.Obs w.Act) (i : w.Index) (n : Nat),
      w.stateAt A i (w.length * n) = (w.member i).start⟩

/-- A class with one of its agents, one of its members and a time, the argument of the vocabulary's
second predicate. -/
abbrev Moment : Type 1 :=
  (w : Trial) × Agent w.Obs w.Act × w.Index × Nat

/-- **The intent record of contract 2**: what makes a class of worlds big, of a class of worlds and
the agent that learns in it. -/
def bigClass : IntentRecord Trial where
  shape := .value _
  dom := []
  props := [goalsReachable, goalsConcealed, frozenShareSmall, successShows, attemptsRecur]
  vocab := [
    ⟨"the agent keeps nothing of its experience", Entrant, fun c => KeepsNothing c.2⟩,
    ⟨"the member's goal is met at the time", Moment,
      fun c => (c.1.member c.2.2.1).goal (c.1.stateAt c.2.1 c.2.2.1 c.2.2.2) = true⟩]

/-- A trial meets the record exactly when each of the five properties holds of it. -/
theorem bigClass_meets {w : Trial} :
    bigClass.Meets w ↔
      goalsReachable.holds w ∧ goalsConcealed.holds w ∧ frozenShareSmall.holds w ∧
        successShows.holds w ∧ attemptsRecur.holds w := by
  constructor
  · intro hm
    have h := hm.2
    exact ⟨h _ (by simp [bigClass]), h _ (by simp [bigClass]), h _ (by simp [bigClass]),
      h _ (by simp [bigClass]), h _ (by simp [bigClass])⟩
  · intro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [bigClass, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

/-! ## The two-door class meets the record -/

/-- A world that asks for a door and never has one: whatever door is tried, it shows that the door
was wrong and asks again. It generates no reward and has no goal. -/
def wall : Member (Option Bool) Bool where
  State := Door
  start := .ask
  observe := fun
    | .ask => none
    | .hit => some true
    | .miss => some false
  reward := fun _ => 0
  step := fun
    | .ask, _ => .miss
    | _, _ => .ask
  goal := fun _ => false

/-- From a state that does not meet a door's goal, a step that does not reach it either is the step
`wall` takes. -/
theorem door_next_wall (pay : Rat) (b : Bool) (A : Agent (Option Bool) Bool) (c : Door × A.Memory)
    (h : (door pay b).goal c.1 = false)
    (h' : (door pay b).goal ((door pay b).next A c).1 = false) :
    (door pay b).next A c = wall.next A c := by
  obtain ⟨s, m⟩ := c
  cases s with
  | ask =>
    have hg : (door pay b).goal
        (bif (A.act m (none, 0)).1 == b then Door.hit else Door.miss) = false := h'
    show ((bif (A.act m (none, 0)).1 == b then Door.hit else Door.miss), (A.act m (none, 0)).2) =
      (Door.miss, (A.act m (none, 0)).2)
    cases hab : (A.act m (none, 0)).1 == b
    · rfl
    · rw [hab] at hg
      have hf : true = false := hg
      exact Bool.noConfusion hf
  | hit =>
    have hf : true = false := h
    exact Bool.noConfusion hf
  | miss => rfl

/-- Up to any time before which no state has met a door's goal, an agent's run in that member is
its run in `wall`. -/
theorem door_run_wall (pay : Rat) (b : Bool) (A : Agent (Option Bool) Bool) :
    ∀ t, (∀ u, u ≤ t → (door pay b).goal ((door pay b).run A u).1 = false) →
      (door pay b).run A t = wall.run A t
  | 0, _ => rfl
  | t + 1, h => by
    have ih := door_run_wall pay b A t (fun u hu => h u (Nat.le_succ_of_le hu))
    show (door pay b).next A ((door pay b).run A t) = wall.next A (wall.run A t)
    rw [← ih]
    exact door_next_wall pay b A _ (h t (Nat.le_succ t)) (h (t + 1) (Nat.le_refl _))

variable (total : List Rat → Rat) (pay : Rat) (X : Agent (Option Bool) Bool)

theorem doors_goalsReachable : goalsReachable.holds (doors total pay X) :=
  fun (A : Agent (Option Bool) Bool) (b : Bool) n => ⟨[b], Nat.lt_succ_self 1, by
    show (door pay b).goal (afterActions (door pay b) ((door pay b).run A (2 * n)).1 [b]) = true
    rw [door_ask]
    cases b <;> rfl⟩

theorem doors_goalsConcealed : goalsConcealed.holds (doors total pay X) :=
  ⟨wall, fun (A : Agent (Option Bool) Bool) (b : Bool) t h => by
    have hs : (door pay b).goal ((door pay b).run A t).1 = false := h t (Nat.le_refl t)
    show ((door pay b).observe ((door pay b).run A t).1,
      (door pay b).reward ((door pay b).run A t).1) =
        (wall.observe (wall.run A t).1, wall.reward (wall.run A t).1)
    rw [← door_run_wall pay b A t h]
    generalize ((door pay b).run A t).1 = s at hs
    cases s with
    | ask => rfl
    | hit =>
      have hf : true = false := hs
      exact Bool.noConfusion hf
    | miss => rfl⟩

theorem doors_frozenShareSmall : frozenShareSmall.holds (doors total pay X) :=
  ⟨1, Nat.lt_succ_self 1, fun (B : Agent (Option Bool) Bool) hB n => by
    rw [doors_solvedCount, doors_solves, doors_solves, keepsNothing_tried pay hB,
      keepsNothing_tried pay hB]
    cases guess B n <;> decide⟩

theorem doors_successShows : successShows.holds (doors total pay X) :=
  ⟨fun (o : Option Bool × Rat) => o.1 == some true,
    fun (A : Agent (Option Bool) Bool) (b : Bool) t => by
    show ((door pay b).observe ((door pay b).run A t).1 == some true) =
      (door pay b).goal ((door pay b).run A t).1
    generalize ((door pay b).run A t).1 = s
    cases s <;> rfl⟩

theorem doors_attemptsRecur : attemptsRecur.holds (doors total pay X) :=
  fun (A : Agent (Option Bool) Bool) (b : Bool) n => door_ask pay b A n

/-- **Every two-door class meets the record**, whatever its aggregation, its payment and its
agent. -/
theorem doors_big : bigClass.Meets (doors total pay X) :=
  bigClass_meets.mpr ⟨doors_goalsReachable total pay X, doors_goalsConcealed total pay X,
    doors_frozenShareSmall total pay X, doors_successShows total pay X,
    doors_attemptsRecur total pay X⟩

/-- O2: the record has no domain hypothesis, the agent that always tries the first door keeps
nothing of its experience, and after one step of `finder`'s run in the first member its goal is
met: an instance of each predicate of the vocabulary. -/
theorem bigClass_o2 : O2 bigClass := by
  refine (o2_correct _).mpr ⟨⟨base, fun _ h => nomatch h⟩, fun p hp => ?_⟩
  simp only [bigClass, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨base, always true⟩, always_keepsNothing true⟩
  · exact ⟨⟨base, finder, true, 1⟩, rfl⟩

/-- O2 before running: `base`, the two-door class of the postcondition's record, meets the whole
record. -/
theorem bigClass_o2Run : O2Run bigClass :=
  (o2Run_correct _).mpr ⟨base, (doors_big List.sum 1 finder).1, (doors_big List.sum 1 finder).2⟩

/-! ## Trials that fail one property each -/

/-- The two-door class with the given members: both counted, attempts of two steps, rewards summed,
and `finder`. -/
def classOf (member : Bool → Member (Option Bool) Bool) : Trial where
  Obs := Option Bool
  Act := Bool
  Index := Bool
  member := member
  counted := [true, false]
  length := 2
  total := List.sum
  agent := finder

/-- `base` whose members have no goal: no state of theirs meets one. -/
def unreachable : Trial := classOf fun b => { door 1 b with goal := fun _ => false }

/-- `base` whose members show their door when they ask for one. -/
def revealing : Trial :=
  classOf fun b =>
    { door 1 b with
      observe := fun (s : Door) =>
        match s with
        | .ask => some b
        | .hit => some true
        | .miss => some false }

/-- `base` whose two members have the same door. -/
def sameDoor : Trial := classOf fun _ => door 1 true

/-- `base` whose members pay nothing and show the same thing whether the door tried was right or
wrong. -/
def hidden : Trial :=
  classOf fun b =>
    { door 0 b with
      observe := fun (s : Door) =>
        match s with
        | .ask => none
        | _ => some false }

/-- `base` whose members never ask again: after the first door is tried they stay where a wrong
door leads. -/
def stuck : Trial :=
  classOf fun b => { door 1 b with step := fun (_ : Door) (_ : Bool) => Door.miss }

/-- O3: each property fails of a trial that changes one part of `base`. -/
theorem bigClass_o3 : O3 bigClass := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [bigClass, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · refine ⟨unreachable, fun h => ?_⟩
    obtain ⟨acts, _, hg⟩ := h finder true 0
    have hf : false = true := hg
    exact Bool.noConfusion hf
  · refine ⟨revealing, fun ⟨R, h⟩ => ?_⟩
    have e := (h finder true 0 (fun u hu => by cases Nat.le_zero.mp hu; rfl)).trans
      (h finder false 0 (fun u hu => by cases Nat.le_zero.mp hu; rfl)).symm
    have e' : some true = some false := congrArg Prod.fst e
    exact absurd e' (by decide)
  · refine ⟨sameDoor, fun ⟨k, hk, h⟩ => ?_⟩
    have h2 : sameDoor.solvedCount (always true) 0 ≤ k :=
      h (always true) (always_keepsNothing true) 0
    have hk' : k < 2 := hk
    have h3 : sameDoor.solvedCount (always true) 0 = 2 := by decide
    omega
  · refine ⟨hidden, fun ⟨signal, h⟩ => ?_⟩
    have h1 : signal (some false, 0) = true := h (always true) true 1
    have h2 : signal (some false, 0) = false := h (always true) false 1
    exact Bool.noConfusion (h1.symm.trans h2)
  · refine ⟨stuck, fun h => ?_⟩
    have e : Door.miss = Door.ask := h finder true 1
    exact absurd e (by decide)

/-- O4: the subject is declared a plain value, of which O4 asks nothing, as in the postcondition's
record. -/
theorem bigClass_o4 : O4 bigClass := (o4_correct _).mpr trivial

/-- O5 with the widest freedom, which every record meets. -/
theorem bigClass_o5_widest : O5 bigClass .widest := o5_widest _

/-- O5 does not hold with equality: `base` and `doubled`, the two models of the postcondition's
record, both meet this record and aggregate one attempt's rewards differently. -/
theorem bigClass_not_o5_eq : ¬ O5 bigClass .eq := by
  refine not_o5_eq (doors_big List.sum 1 finder) (doors_big (fun l => l.sum + l.sum) 1 finder)
    fun h => ?_
  have ht : base.total [1] = doubled.total [1] := congrArg (fun w : Trial => w.total [1]) h
  exact absurd ht (by decide +kernel)

/-- The pair obligation of each property's pair whose only input is trivial, in the class of every
subject: `base` fulfils each property. -/
theorem bigClass_pairs :
    ∀ c ∈ bigClass.props, OPair (Pair.whole bigClass c) (fun _ => True) :=
  fun c hc => (oPair_whole_iff _ _ _).mpr
    ⟨base, trivial, fun _ => (doors_big List.sum 1 finder).2 c hc⟩

end AcornVerif.Intent.BigClass
