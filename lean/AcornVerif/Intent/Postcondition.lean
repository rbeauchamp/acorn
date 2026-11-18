/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.PostconditionSubject

/-!
# Intent record: what achieving goals promises

The postcondition of Acorn's mission contract (`docs/mission-contract.md`, section "The
postcondition: what achieves goals promises") opens with six plain sentences that the owner
confirmed on 2026-11-03 as the statement of what achieving goals promises, with two forks the owner
decided that day: under fork F-A the promise is stated in reward, and under fork F-B the advantage
is promised eventually, with a bound on how long learning takes to come next. The agents that work
on Acorn wrote that restatement from a research report on the research of Rich Sutton, Khurram
Javed and Oak Lab, and the owner adopted it by confirming it. On 2026-11-17 the owner decided how
the record reads "it keeps solving it" of an agent that goes on exploring (rbeauchamp/acorn#248):
once the agent has solved a member, it solves it again on every later attempt before a stated
attempt, but for at most a stated number of them, while the member's attempts start from the same
state. The owner decided the same day that the advantage is read before that stated attempt as
well, early enough that the promise of solving again still applies to it. On 2026-11-18, asked
whether the stated number is how many later attempts the agent may miss, the owner answered that it
is. The restatement and those answers, in those words, are this record's only sources; the Lean
form each takes below is the agents', made on the owner's behalf, and the owner has not seen it.

The record's writer had read, before writing it: the mission contract, whose design sections state
proposed Lean forms of separation and retention over the kernel's definitions; the records of
contracts 1 and 3, `AcornVerif.Intent.WorldInterface.worldInterface` and
`AcornVerif.Intent.OneStream.oneStream`; the sections of the design document `docs/design.md` on
classes of worlds, on concealed goals and visits, and on the OaK picture and the executed agent; the
baseline assessment, the frontier and, of the prior-art register, its qualification table and its
two assessments not admitted; and the issues open on 2026-11-10, with the closed
rbeauchamp/acorn#140, whose text derives facts about the executed agent's controller. Of the modules
that define the kernel's worlds, classes and visits the writer had read the first line of three
declarations (`Conceals`, `SolvesOnVisit` and `BigClass`), found by a search for their names, and no
more; of the executing agent's code, nothing. The property on solving again and the tie of the
advantage to the horizon are not written that blind: their form, an attempt before which they are
read and a count of lapses, was chosen by a writer that had read how the executing agent explores,
because an agent that goes on exploring is what the owner's decisions of 2026-11-17 are about. The
fourth property, `learnsAgain`, has the form it was given on 2026-11-18, when the record was
compared with two blind readings of the owner's words by another provider's model; the record's
confirmation file, `lean/AcornVerif/Intent/Postcondition.md`, says what they found. The record
imports nothing of Acorn's but the module of its subject's types,
`AcornVerif.Intent.PostconditionSubject`, and through it contract 1's record module and the bridge
to lean-intent.

The subject, `Trial`, is a class of worlds with what the class states, and the agent that learns
in it. What the second sentence says a class states: the members, each a world over the class's
observations and actions with its reward and its goal (`Member`); the members the comparison
counts (`counted`); how long an attempt lasts (`length`); and how an attempt's rewards are
aggregated (`total`). What the decisions of 2026-11-17 add: the attempt before which the class
reads its promises of the advantage and of solving again (`horizon`), and on how many attempts
before it the agent may fail a member it has solved (`lapses`). Every quantity the properties read
is computed from those by the faithful run of an agent in a member (`Member.run`), which is
contract 1's faithful run never stopped
(`run_reaches`, in the module of this record's consequences): the agent is given the world's
observation and reward at each step, the world moves by its own dynamics on the agent's action,
restarts included, and the agent keeps the memory its answer produced. Attempt `n` of a run is its
`length` steps from step `length * n` on. So the record reads each compared agent in a run of its
own in each member, from that agent's initial memory, with its memory carried across that member's
attempts. A class that presents several members in one stream is not this subject.

The four properties are the record's reading of sentences 2 to 5:

* `rewardCountsMembers` is sentence 2: among the agents compared, on every pair of attempts, one
  earns more reward across the counted members than the other exactly when it solves more of them.
* `earnsMoreInTime` is sentence 3 with the first half of sentence 5: on some attempt the agent
  earns more reward across the counted members than any agent that keeps nothing of its experience
  earns on any attempt. That attempt comes before the class's horizon, as the owner decided on
  2026-11-17, and leaves more later attempts before it than the class's number of lapses, which is
  how the record reads "early enough that the promise of solving again still applies to it". The
  record names no bound on it that holds of every class, which is the bound fork F-B leaves to the
  next step: each class names its own horizon.
* `keepsSolving` is the first half of sentence 4, with "the problem stays the same" read as: the
  member's attempts start from the same state of its world, and "it keeps solving it" read as the
  owner decided on 2026-11-17 and confirmed on 2026-11-18: on every later attempt before the
  class's horizon, except on at most as many of them as the class's number of lapses, which the
  agent may miss. With no lapse allowed it asks every such attempt.
* `learnsAgain` is the second half of sentence 4: where a member's attempts have left the state
  from which the agent once solved it and have come back to that state for good, the agent solves
  it again on some later attempt. No attempt is named by which it does, as sentence 4 names none,
  and nothing is asked where the member's attempts never left that state, which is the case of
  `keepsSolving`.

Sentence 1, and "success is measured as reward" of sentence 5, are carried by stating the first two
properties in the reward each member's world generates and the run gives the agent. Sentence 6
promises nothing, so it adds no property; what the record allows under it is shown by its models.
The record has no domain hypothesis.

Decided on the owner's behalf, each checked against the second, blind readings and recorded in
the record's confirmation file, with its reason:

* A goal is a decidable condition on a member's states.
* The agents compared each run alone in each member; campaigns of several members in one stream are
  left to obligation 10 of the mission contract.
* "The problem stays the same" is equality of the world's state at the start of the attempts.
* `learnsAgain` asks an agent to solve again, at some time, a member whose problem went away and
  has come back for good. It does not ask how soon, and it does not ask that the agent could solve
  a problem that is never put to it again. Whether the ability is promised for the agent's whole
  life, and its form for campaigns, stay with obligation 10 of the mission contract.
* The lapses are counted for each member: one list of at most the class's number of attempts, the
  same whichever earlier attempt solved the member. The record does not say why an attempt is a
  lapse, and reads no report of the agent's about its own exploring.
* A class names its horizon and its number of lapses. The record asks of them only room for the
  attempt of the advantage, which leaves more later attempts before the horizon than the lapses:
  no agent meets the record in a class that allows as many lapses as it has attempts before its
  horizon, less one (`unmet_of_lapses`, in the module of this record's consequences). The more
  lapses a class allows, the less its promise of solving again asks.
* `earnsMoreInTime` asks for one attempt, not for every attempt from some attempt on. With
  `keepsSolving`, each member the agent has solved it solves again on the later attempts before
  the horizon that are not that member's lapses, where the member's problem stays the same; and
  since the attempt of the advantage leaves more later attempts than the lapses, each member
  solved on it is solved on at least one of them (`advantageSolvedAgain_holds`, in the module of
  this record's consequences).
* "The attempts counted" are all of them: `rewardCountsMembers` holds on every attempt of each
  compared agent.
* The comparison counts a finite list of members that the class names, while `keepsSolving` and
  `learnsAgain` are asked of every member.

Each property's plain words were written from the finished predicate and are trusted, not proved.
What the owner confirmed is the six sentences and the three answers above; that this record carries
them is the agents' judgment.
-/

namespace AcornVerif.Intent.Postcondition

open LeanIntent WorldInterface

namespace Member

variable {Obs Act : Type}

/-- One step of the faithful run of the agent `A` in the member `M`, from the world's state and the
agent's memory: the agent is given the world's observation and reward, the world moves by its own
dynamics on the agent's action, and the agent keeps the memory its answer produced. -/
def next (M : Member Obs Act) (A : Agent Obs Act) (c : M.State × A.Memory) : M.State × A.Memory :=
  (M.step c.1 (A.act c.2 (M.observe c.1, M.reward c.1)).1,
    (A.act c.2 (M.observe c.1, M.reward c.1)).2)

/-- The faithful run of the agent `A` in the member `M`, never stopped: the world's state and the
agent's memory after `t` steps, from the world's start and the agent's initial memory. -/
def run (M : Member Obs Act) (A : Agent Obs Act) : Nat → M.State × A.Memory
  | 0 => (M.start, A.initial)
  | t + 1 => M.next A (M.run A t)

end Member

/-- An agent keeps nothing of its experience when the memory its answer produces does not depend on
what it was given: its memory advances the same way whatever it perceives, though its action may
read what it is given at that step. -/
def KeepsNothing {Obs Act : Type} (A : Agent Obs Act) : Prop :=
  ∀ m o o', (A.act m o).2 = (A.act m o').2

namespace Trial

variable (w : Trial)

/-- The state of the member `i`'s world after `t` steps of the agent `A`'s run in it. -/
def stateAt (A : Agent w.Obs w.Act) (i : w.Index) (t : Nat) : (w.member i).State :=
  ((w.member i).run A t).1

/-- The times of attempt `n`: its `length` steps, from `length * n` on. -/
def attemptTimes (n : Nat) : List Nat :=
  (List.range w.length).map (w.length * n + ·)

/-- Whether the agent `A` solves the member `i` on attempt `n`: its run in that member is in a
state that meets the member's goal at some time of the attempt. -/
def solves (A : Agent w.Obs w.Act) (i : w.Index) (n : Nat) : Bool :=
  (w.attemptTimes n).any fun t => (w.member i).goal (w.stateAt A i t)

/-- The reward the agent `A` earns in the member `i` on attempt `n`: the class's aggregate of the
rewards the member's world generates, and the run gives the agent, at the times of the attempt. -/
def earned (A : Agent w.Obs w.Act) (i : w.Index) (n : Nat) : Rat :=
  w.total ((w.attemptTimes n).map fun t => (w.member i).reward (w.stateAt A i t))

/-- The reward the agent `A` earns across the class on attempt `n`: the sum, over the counted
members, of what it earns on that attempt of its run in each. -/
def classReward (A : Agent w.Obs w.Act) (n : Nat) : Rat :=
  (w.counted.map fun i => w.earned A i n).sum

/-- How many of the counted members the agent `A` solves on attempt `n`. -/
def solvedCount (A : Agent w.Obs w.Act) (n : Nat) : Nat :=
  (w.counted.filter fun i => w.solves A i n).length

/-- The agents compared: the agent that learns, and every agent that keeps nothing of its
experience. -/
def Compared (A : Agent w.Obs w.Act) : Prop :=
  A = w.agent ∨ KeepsNothing A

/-- The member `i` poses on attempt `n'` the problem it posed on attempt `n`: in the learning
agent's run, its world is at the start of attempt `n'` in the state it was in at the start of
attempt `n`. -/
def SameProblem (i : w.Index) (n n' : Nat) : Prop :=
  w.stateAt w.agent i (w.length * n') = w.stateAt w.agent i (w.length * n)

end Trial

/-! ## The properties -/

/-- Among the agents compared, on every pair of attempts, one earns more reward across the counted
members than the other exactly when it solves more of them. -/
def rewardCountsMembers : Clause Trial :=
  ⟨"among the agents compared, and for any attempt of each, one earns more reward across the \
    class on its attempt than the other on its own exactly when it solves more members on it",
    fun w =>
    ∀ A B, w.Compared A → w.Compared B → ∀ n k,
      (w.classReward B k < w.classReward A n ↔ w.solvedCount B k < w.solvedCount A n)⟩

/-- There is an attempt, with more later attempts before the class's horizon than the class's
number of lapses, on which the agent earns more reward across the counted members than any agent
that keeps nothing of its experience earns on any attempt. -/
def earnsMoreInTime : Clause Trial :=
  ⟨"on some attempt that leaves more later attempts before a stated attempt than a stated number \
    of lapses, the agent earns more reward across the class than any agent that keeps nothing of \
    its experience earns on any attempt", fun w =>
    ∃ n, n + w.lapses + 1 < w.horizon ∧
      ∀ B, KeepsNothing B → ∀ k, w.classReward B k < w.classReward w.agent n⟩

/-- Once the agent has solved a member on an attempt, it solves it on every later attempt before
the class's horizon up to which that member's attempts all start from the state the solved attempt
started from, except on at most as many attempts as the class's number of lapses: for each member,
it solves it on the attempts outside one list of at most that many. -/
def keepsSolving : Clause Trial :=
  ⟨"once the agent has solved a member, it solves it again on every later attempt before a \
    stated attempt, but for at most a stated number of them, while the member's attempts start \
    from the same state", fun w =>
    ∀ i, ∃ lapsed : List Nat, lapsed.length ≤ w.lapses ∧
      ∀ n n', n ≤ n' → n' < w.horizon → (∀ k, n ≤ k → k ≤ n' → w.SameProblem i n k) →
        w.solves w.agent i n = true → n' ∉ lapsed → w.solves w.agent i n' = true⟩

/-- Once the agent has solved a member on an attempt, if a later attempt of the member starts from
another state than that attempt, and every attempt from some still later attempt on starts from the
state the solved attempt started from, then the agent solves the member on some attempt after the
one that started from the other state. Asked of every such attempt, this is one solve after the last
of them, on or after the first attempt from which the member is back for good. No attempt is named
by which it comes, and nothing is asked of a member whose attempts never leave that state or never
come back to it for good. -/
def learnsAgain : Clause Trial :=
  ⟨"once the agent has solved a member, and the member's attempts have left the state the solved \
    one started from and come back to it for good, it solves the member again on some later \
    attempt", fun w =>
    ∀ i n g n', n < g → g < n' → ¬ w.SameProblem i n g → (∀ k, n' ≤ k → w.SameProblem i n k) →
      w.solves w.agent i n = true → ∃ n'', g < n'' ∧ w.solves w.agent i n'' = true⟩

/-- A class with one of its agents, the argument of the vocabulary's first predicate. -/
abbrev Entrant : Type 1 :=
  (w : Trial) × Agent w.Obs w.Act

/-- A class with one of its agents, one of its members and an attempt, the argument of the
vocabulary's second predicate. -/
abbrev Attempt : Type 1 :=
  (w : Trial) × Agent w.Obs w.Act × w.Index × Nat

/-- **The intent record of the postcondition**: what achieving goals promises of a class of worlds
and the agent that learns in it. -/
def postcondition : IntentRecord Trial where
  shape := .value _
  dom := []
  props := [rewardCountsMembers, earnsMoreInTime, keepsSolving, learnsAgain]
  vocab := [
    ⟨"the agent keeps nothing of its experience", Entrant, fun c => KeepsNothing c.2⟩,
    ⟨"the agent solves the member on the attempt", Attempt,
      fun c => c.1.solves c.2.1 c.2.2.1 c.2.2.2 = true⟩]

/-- A trial meets the record exactly when each of the four properties holds of it. -/
theorem postcondition_meets {w : Trial} :
    postcondition.Meets w ↔
      rewardCountsMembers.holds w ∧ earnsMoreInTime.holds w ∧ keepsSolving.holds w ∧
        learnsAgain.holds w := by
  constructor
  · intro hm
    have h := hm.2
    exact ⟨h _ (by simp [postcondition]), h _ (by simp [postcondition]),
      h _ (by simp [postcondition]), h _ (by simp [postcondition])⟩
  · intro ⟨h1, h2, h3, h4⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [postcondition, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4

/-! ## The two-door class -/

/-- The states of a member of the two-door class. -/
inductive Door where
  /-- The world asks for a door. -/
  | ask
  /-- The door just tried was the member's. -/
  | hit
  /-- The door just tried was not the member's. -/
  | miss
  deriving DecidableEq

/-- The member of the two-door class whose door is `b`. Asked for a door, it moves to `hit` when the
door tried is `b` and to `miss` otherwise, shows which, and then asks again whatever the action. It
generates the reward `pay` at `hit` and none elsewhere, and its goal is `hit`. -/
def door (pay : Rat) (b : Bool) : Member (Option Bool) Bool where
  State := Door
  start := .ask
  observe := fun
    | .ask => none
    | .hit => some true
    | .miss => some false
  reward := fun
    | .hit => pay
    | _ => 0
  step := fun
    | .ask, a => bif a == b then .hit else .miss
    | _, _ => .ask
  goal := fun
    | .hit => true
    | _ => false

/-- The two-door class with the aggregation `total`, the payment `pay` and the agent `A`: one member
for each door, both counted, and attempts of two steps, one to try a door and one to see the
outcome. Its promises are read over its first three attempts, and it allows no lapse. -/
def doors (total : List Rat → Rat) (pay : Rat) (A : Agent (Option Bool) Bool) : Trial where
  Obs := Option Bool
  Act := Bool
  Index := Bool
  member := door pay
  counted := [true, false]
  length := 2
  total := total
  horizon := 3
  lapses := 0
  agent := A

/-- The door the agent `A` tries on attempt `n` of its run in the member `b`: its action at the
attempt's first step. -/
def tried (pay : Rat) (A : Agent (Option Bool) Bool) (b : Bool) (n : Nat) : Bool :=
  (A.act ((door pay b).run A (2 * n)).2
    ((door pay b).observe ((door pay b).run A (2 * n)).1,
      (door pay b).reward ((door pay b).run A (2 * n)).1)).1

/-- Two steps after it asks for a door, a member asks again. -/
theorem door_restart (pay : Rat) (b a a' : Bool) :
    (door pay b).step ((door pay b).step Door.ask a) a' = Door.ask := by
  cases a <;> cases b <;> rfl

/-- Every attempt of every agent's run in a member starts with the member asking for a door. -/
theorem door_ask (pay : Rat) (b : Bool) (A : Agent (Option Bool) Bool) :
    ∀ n, ((door pay b).run A (2 * n)).1 = Door.ask
  | 0 => rfl
  | n + 1 => by
    have h := door_ask pay b A n
    show (door pay b).step ((door pay b).step ((door pay b).run A (2 * n)).1 _) _ = Door.ask
    rw [h]
    exact door_restart pay b _ _

/-- At an attempt's second step the member is at `hit` exactly when the door tried is its own. -/
theorem door_tried (pay : Rat) (b : Bool) (A : Agent (Option Bool) Bool) (n : Nat) :
    ((door pay b).run A (2 * n + 1)).1 = bif tried pay A b n == b then Door.hit else Door.miss := by
  show (door pay b).step ((door pay b).run A (2 * n)).1 (tried pay A b n) = _
  rw [door_ask]
  rfl

variable (total : List Rat → Rat) (pay : Rat) (X A : Agent (Option Bool) Bool)

/-- An agent solves a member of the two-door class on an attempt exactly when the door it tries is
the member's. -/
theorem doors_solves (b : Bool) (n : Nat) :
    (doors total pay X).solves A b n = (tried pay A b n == b) := by
  show ((door pay b).goal ((door pay b).run A (2 * n)).1 ||
    ((door pay b).goal ((door pay b).run A (2 * n + 1)).1 || false)) = _
  rw [door_tried, door_ask]
  cases tried pay A b n == b <;> rfl

/-- In a two-door class, every member's attempts start from the same state in the agent's run. -/
theorem doors_sameProblem (b : Bool) (n k : Nat) : (doors total pay X).SameProblem b n k :=
  (door_ask pay b X k).trans (door_ask pay b X n).symm

/-- What a member of the two-door class pays on an attempt, by whether it is solved: the class's
aggregate of no reward at the first step and, at the second, the payment or none. -/
def paid (s : Bool) : Rat :=
  total [0, bif s then pay else 0]

/-- What an agent earns in a member of the two-door class on an attempt. -/
theorem doors_earned (b : Bool) (n : Nat) :
    (doors total pay X).earned A b n = paid total pay ((doors total pay X).solves A b n) := by
  rw [doors_solves]
  show total [(door pay b).reward ((door pay b).run A (2 * n)).1,
    (door pay b).reward ((door pay b).run A (2 * n + 1)).1] = _
  rw [door_tried, door_ask]
  cases tried pay A b n == b <;> rfl

/-- What an agent earns across the two-door class on an attempt. -/
theorem doors_classReward (n : Nat) :
    (doors total pay X).classReward A n =
      paid total pay ((doors total pay X).solves A true n) +
        (paid total pay ((doors total pay X).solves A false n) + 0) := by
  show (doors total pay X).earned A true n + ((doors total pay X).earned A false n + 0) = _
  rw [doors_earned, doors_earned]

/-- How many of two members are solved. -/
def tally (s t : Bool) : Nat :=
  (bif s then 1 else 0) + (bif t then 1 else 0)

/-- How many members of the two-door class an agent solves on an attempt. -/
theorem doors_solvedCount (n : Nat) :
    (doors total pay X).solvedCount A n =
      tally ((doors total pay X).solves A true n) ((doors total pay X).solves A false n) := by
  show ([true, false].filter fun i => (doors total pay X).solves A i n).length = _
  cases h1 : (doors total pay X).solves A true n <;>
    cases h2 : (doors total pay X).solves A false n <;> simp only [List.filter, h1, h2] <;> rfl

/-- The aggregation and the payment of a two-door class are fair when, for any two outcomes of an
attempt, the one with more members solved is the one that pays more across the class. -/
def Fair : Prop :=
  ∀ s1 s2 s3 s4 : Bool,
    (paid total pay s3 + (paid total pay s4 + 0) < paid total pay s1 + (paid total pay s2 + 0) ↔
      tally s3 s4 < tally s1 s2)

/-- In a two-door class with a fair aggregation and payment, every two agents on every two attempts
are ordered by reward as they are by members solved. -/
theorem doors_rewardCounts (h : Fair total pay) :
    rewardCountsMembers.holds (doors total pay X) :=
  fun (A B : Agent (Option Bool) Bool) _ _ n k => by
    rw [doors_classReward, doors_classReward, doors_solvedCount, doors_solvedCount]
    exact h _ _ _ _

/-! ## Agents that keep nothing -/

/-- The memory an agent holds after `t` steps in which it is given `o` every time. -/
def drift {Obs Act : Type} (B : Agent Obs Act) (o : Obs × Rat) : Nat → B.Memory
  | 0 => B.initial
  | t + 1 => (B.act (drift B o t) o).2

/-- An agent that keeps nothing of its experience holds, after `t` steps of its run in any member,
the memory it would hold had it been given the same thing every time. -/
theorem keepsNothing_memory {Obs Act : Type} {B : Agent Obs Act} (h : KeepsNothing B)
    (M : Member Obs Act) (o : Obs × Rat) : ∀ t, (M.run B t).2 = drift B o t
  | 0 => rfl
  | t + 1 => by
    show (B.act (M.run B t).2 _).2 = (B.act (drift B o t) o).2
    rw [keepsNothing_memory h M o t]
    exact h _ _ _

/-- The door an agent tries on attempt `n` when it has been shown nothing and paid nothing. -/
def guess (B : Agent (Option Bool) Bool) (n : Nat) : Bool :=
  (B.act (drift B (none, 0) (2 * n)) (none, 0)).1

/-- An agent that keeps nothing of its experience tries the same door in both members of the
two-door class on each attempt. -/
theorem keepsNothing_tried {B : Agent (Option Bool) Bool} (h : KeepsNothing B) (b : Bool)
    (n : Nat) : tried pay B b n = guess B n := by
  unfold tried
  rw [door_ask, keepsNothing_memory h (door pay b) (none, 0)]
  rfl

/-- The agent that always answers with one action keeps nothing of its experience. -/
theorem always_keepsNothing {Obs Act : Type} (a : Act) : KeepsNothing (always (Obs := Obs) a) :=
  fun _ _ _ => rfl

/-! ## An agent that learns the two-door class -/

/-- An agent for the two-door class that remembers the door that worked. Asked for a door, it tries
the door it knows, or the first door when it knows none, and remembers which it tried. Shown the
outcome, it comes to know the door: the one it tried when that was right, and the other one when it
was wrong. -/
def finder : Agent (Option Bool) Bool where
  Memory := Option Bool × Bool
  initial := (none, true)
  act := fun m o =>
    match o.1 with
    | none => (m.1.getD true, (m.1, m.1.getD true))
    | some true => (true, (some m.2, m.2))
    | some false => (true, (some (!m.2), m.2))

/-- Once `finder` knows a member's door, one attempt later the member asks again and `finder` still
knows the door. -/
theorem finder_round (b x : Bool) :
    (door pay b).next finder ((door pay b).next finder (Door.ask, (some b, x))) =
      (Door.ask, (some b, b)) := by
  cases b <;> rfl

/-- From its second attempt on, `finder` starts each attempt of its run in a member knowing that
member's door. -/
theorem finder_knows (b : Bool) :
    ∀ n, ∃ x, (door pay b).run finder (2 * (n + 1)) = (Door.ask, (some b, x))
  | 0 => by cases b <;> exact ⟨_, rfl⟩
  | n + 1 => by
    obtain ⟨x, h⟩ := finder_knows b n
    refine ⟨b, ?_⟩
    show (door pay b).next finder ((door pay b).next finder
      ((door pay b).run finder (2 * (n + 1)))) = _
    rw [h]
    exact finder_round pay b x

/-- From its second attempt on, `finder` solves every member of the two-door class. -/
theorem finder_solves (b : Bool) (n : Nat) :
    (doors total pay X).solves finder b (n + 1) = true := by
  obtain ⟨x, h⟩ := finder_knows pay b n
  rw [doors_solves]
  unfold tried
  rw [h]
  cases b <;> rfl

/-- **A two-door class with a fair aggregation and payment, and `finder`, meets the record.** -/
theorem doors_finder_meets (h : Fair total pay) :
    postcondition.Meets (doors total pay finder) := by
  refine postcondition_meets.mpr ⟨doors_rewardCounts total pay finder h,
    ⟨1, show 1 + 0 + 1 < 3 by decide, fun (B : Agent (Option Bool) Bool) hB k => ?_⟩,
    fun b => ⟨[], Nat.le_refl 0, fun n n' hle _ _ hs _ => ?_⟩,
    fun b n g _ _ _ left _ _ => absurd (doors_sameProblem total pay finder b n g) left⟩
  · show (doors total pay finder).classReward B k < (doors total pay finder).classReward finder 1
    rw [doors_classReward, doors_classReward, finder_solves, finder_solves, doors_solves,
      doors_solves, keepsNothing_tried pay hB, keepsNothing_tried pay hB]
    exact (h _ _ _ _).mpr (by cases guess B k <;> decide)
  · cases n' with
    | zero => exact (Nat.le_zero.mp hle) ▸ hs
    | succ n' => exact finder_solves ..

/-- Summing an attempt's rewards, with a payment of one, is fair. -/
theorem fair_sum_one : Fair List.sum 1 := by
  intro s1 s2 s3 s4
  cases s1 <;> cases s2 <;> cases s3 <;> cases s4 <;> decide +kernel

/-- The two-door class that sums an attempt's rewards and pays one, with `finder`: the model each
refuting trial below changes one part of. -/
def base : Trial := doors List.sum 1 finder

theorem base_meets : postcondition.Meets base :=
  doors_finder_meets _ _ fair_sum_one

/-- O2: the record has no domain hypothesis, the agent that always tries the first door keeps
nothing of its experience, and `finder` solves the first member on its first attempt: an instance of
each predicate of the vocabulary. -/
theorem postcondition_o2 : O2 postcondition := by
  refine (o2_correct _).mpr ⟨⟨base, fun _ h => nomatch h⟩, fun p hp => ?_⟩
  simp only [postcondition, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨⟨base, always true⟩, always_keepsNothing true⟩
  · exact ⟨⟨base, finder, true, 0⟩, rfl⟩

/-- O2 before running: `base` meets the whole record. -/
theorem postcondition_o2Run : O2Run postcondition :=
  (o2Run_correct _).mpr ⟨base, base_meets.1, base_meets.2⟩

/-! ## A class whose member's problem leaves and comes back -/

/-- The states of the detour world. -/
inductive Spot where
  /-- The world asks for the move that solves it. -/
  | home
  /-- The move just made solved it. -/
  | won
  /-- The move just made did not solve it. -/
  | lost
  /-- The world is away from its problem: whatever the moves, it is next at `idle` and then at
  `home`. -/
  | away
  /-- The second step of an attempt that started away. -/
  | idle
  deriving DecidableEq

/-- The moves of the detour world. -/
inductive Move where
  /-- The move that solves the world's problem at `home`. -/
  | solve
  /-- A move that neither solves nor leaves. -/
  | wait
  /-- The move that, from `won` or `lost`, starts the next attempt away. -/
  | leave
  deriving DecidableEq

/-- The detour world. At `home` the move `solve` wins and every other move loses. After either, the
move `leave` starts the next attempt `away`, and every other move starts it at `home`. An attempt
that starts `away` ends at `home` whatever the moves. The world generates the reward one at `won`
and none elsewhere, and its goal is `won`. -/
def detour : Member Unit Move where
  State := Spot
  start := .home
  observe := fun _ => ()
  reward := fun
    | .won => 1
    | _ => 0
  step := fun
    | .home, .solve => .won
    | .home, _ => .lost
    | .won, .leave => .away
    | .lost, .leave => .away
    | .away, _ => .idle
    | _, _ => .home
  goal := fun
    | .won => true
    | _ => false

/-- The detour class with the agent `A`: its one member, counted, and attempts of two steps. Its
promises of the advantage and of solving again are read over its first eight attempts, and it allows
no lapse. -/
def detours (A : Agent Unit Move) : Trial where
  Obs := Unit
  Act := Move
  Index := Unit
  member := fun _ => detour
  counted := [()]
  length := 2
  total := List.sum
  horizon := 8
  lapses := 0
  agent := A

/-- An agent for the detour world that solves on its first step, leaves on its second and waits
ever after. Its memory counts its steps. -/
def quits : Agent Unit Move where
  Memory := Nat
  initial := 0
  act := fun m _ =>
    (match m with
      | 0 => .solve
      | 1 => .leave
      | _ + 2 => .wait, m + 1)

/-- After `t` steps of its run in any member, `quits` has counted `t` steps. -/
theorem quits_memory (M : Member Unit Move) : ∀ t, (M.run quits t).2 = t
  | 0 => rfl
  | t + 1 => congrArg (· + 1) (quits_memory M t)

/-- From its third attempt on, the run of `quits` in the detour world starts each attempt at `home`
and loses it. -/
theorem quits_late : ∀ j, (detour.run quits (2 * j + 4)).1 = Spot.home ∧
    (detour.run quits (2 * j + 5)).1 = Spot.lost
  | 0 => ⟨rfl, rfl⟩
  | j + 1 => by
    obtain ⟨_, lost⟩ := quits_late j
    have home : (detour.run quits (2 * (j + 1) + 4)).1 = Spot.home := by
      show detour.step (detour.run quits (2 * j + 5)).1
        (quits.act (detour.run quits (2 * j + 5)).2 _).1 = Spot.home
      rw [lost, quits_memory]
      rfl
    refine ⟨home, ?_⟩
    show detour.step (detour.run quits (2 * (j + 1) + 4)).1
      (quits.act (detour.run quits (2 * (j + 1) + 4)).2 _).1 = Spot.lost
    rw [home, quits_memory]
    rfl

/-- The detour class with `quits`: its agent solves the member on its first attempt, the member's
second attempt starts away, every later attempt starts at `home` again, and the agent never solves
the member again. -/
def quitting : Trial := detours quits

/-- From its third attempt on, `quits` does not solve the member of the detour class. -/
theorem quitting_misses (n : Nat) : quitting.solves quits () (n + 2) = false := by
  obtain ⟨home, lost⟩ := quits_late n
  have e : 2 * (n + 2) = 2 * n + 4 := by omega
  show (detour.goal (detour.run quits (2 * (n + 2) + 0)).1 ||
    (detour.goal (detour.run quits (2 * (n + 2) + 1)).1 || false)) = false
  rw [Nat.add_zero, e, home, show (detour.run quits (2 * n + 4 + 1)).1 = Spot.lost from lost]
  rfl

/-- From its third attempt on, the member of `quitting` starts each attempt from the state its first
attempt started from. -/
theorem quitting_back (k : Nat) (late : 2 ≤ k) : quitting.SameProblem () 0 k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have e : 2 * (j + 2) = 2 * j + 4 := by omega
  show (detour.run quits (2 * (j + 2))).1 = (detour.run quits (2 * 0)).1
  rw [e, (quits_late j).1]
  rfl

/-- The second attempt of the member of `quitting` starts from another state than the first. -/
theorem quitting_left : ¬ quitting.SameProblem () 0 1 :=
  fun h => Spot.noConfusion (h : Spot.away = Spot.home)

/-- `quitting` fails the record's fourth property: its agent solves the member on its first attempt,
the second attempt starts from another state, every attempt from the third on starts from the first
one's state, and the agent solves the member on none of them. -/
theorem quitting_fails : ¬ learnsAgain.holds quitting := fun h => by
  obtain ⟨n'', late, hs⟩ := h () 0 1 2 (by decide) (by decide) quitting_left
    (fun k hk => quitting_back k hk) rfl
  obtain ⟨m, rfl⟩ : ∃ m, n'' = m + 2 := ⟨n'' - 2, by omega⟩
  exact Bool.noConfusion (hs.symm.trans (quitting_misses m))

/-- `quits` keeps nothing of its experience: its memory counts its steps. -/
theorem quits_keepsNothing : KeepsNothing quits :=
  fun _ _ _ => rfl

/-! ## Trials that fail one property each -/

/-- `base` whose members pay nothing: reward does not show which members were solved. -/
def unpaid : Trial := doors List.sum 0 finder

/-- `base` whose agent always tries the first door, so keeps nothing of its experience. -/
def fixed : Trial := doors List.sum 1 (always true)

/-- An agent that tries the first door on its first step and the other door ever after. Its memory
counts its steps. -/
def once : Agent (Option Bool) Bool where
  Memory := Nat
  initial := 0
  act := fun m _ => (m == 0, m + 1)

/-- `base` whose agent is `once`: it solves the first member on its first attempt and never
again. -/
def forgetful : Trial := doors List.sum 1 once

/-- An agent that keeps nothing of its experience fails `earnsMoreInTime` in every class: on no
attempt does it earn more than itself. -/
theorem not_earnsMore_of_keepsNothing {w : Trial} (h : KeepsNothing w.agent) :
    ¬ earnsMoreInTime.holds w :=
  fun ⟨n, _, hn⟩ => Rat.lt_irrefl (hn w.agent h n)

/-- O3: each property fails of some trial. The first three fail of a trial that changes one part of
`base`, and the fourth of `quitting`, in whose class a member's attempts leave the state of a solved
attempt and come back to it. -/
theorem postcondition_o3 : O3 postcondition := by
  refine (o3_correct _).mpr fun p hp => ?_
  simp only [postcondition, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · refine ⟨unpaid, fun h => ?_⟩
    have hlt : unpaid.classReward (always true) 0 < unpaid.classReward finder 1 :=
      (h finder (always true) (.inl rfl) (.inr (always_keepsNothing true)) 1 0).mpr (by decide)
    exact absurd hlt (by decide +kernel)
  · exact ⟨fixed, not_earnsMore_of_keepsNothing (w := fixed) (always_keepsNothing true)⟩
  · refine ⟨forgetful, fun h => ?_⟩
    obtain ⟨lapsed, few, keeps⟩ := h true
    have none : lapsed = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp few)
    have hs : forgetful.solves once true 1 = true :=
      keeps 0 1 (by decide) (by decide)
        (fun k _ _ => doors_sameProblem List.sum 1 once true 0 k) rfl
        (by rw [none]; exact List.not_mem_nil)
    exact absurd hs (by decide)
  · exact ⟨quitting, quitting_fails⟩

/-- O4: the subject is declared a plain value, of which O4 asks nothing: a class of worlds with an
agent is a description, whose worlds and agent the properties read through their runs. -/
theorem postcondition_o4 : O4 postcondition := (o4_correct _).mpr trivial

/-- O5 with the widest freedom, which every record meets. -/
theorem postcondition_o5_widest : O5 postcondition .widest := o5_widest _

/-- Counting each attempt's summed rewards twice, with a payment of one, is fair. -/
theorem fair_double_one : Fair (fun l => l.sum + l.sum) 1 := by
  intro s1 s2 s3 s4
  cases s1 <;> cases s2 <;> cases s3 <;> cases s4 <;> decide +kernel

/-- `base` with each attempt's summed rewards counted twice: a second model of the record. -/
def doubled : Trial := doors (fun l => l.sum + l.sum) 1 finder

theorem doubled_meets : postcondition.Meets doubled :=
  doors_finder_meets _ _ fair_double_one

/-- O5 does not hold with equality: `base` and `doubled` both meet the record and aggregate one
attempt's rewards differently. -/
theorem postcondition_not_o5_eq : ¬ O5 postcondition .eq := by
  refine not_o5_eq base_meets doubled_meets fun h => ?_
  have ht : base.total [1] = doubled.total [1] := congrArg (fun w : Trial => w.total [1]) h
  exact absurd ht (by decide +kernel)

/-- The pair obligation of each property's pair whose only input is trivial, in the class of every
subject: `base` fulfils each property. The pair whose input is the class of worlds is stated with
the record of contract 2, which says which classes a learning agent can be asked to serve
(`AcornVerif.Intent.BigClass.Served`). -/
theorem postcondition_pairs :
    ∀ c ∈ postcondition.props, OPair (Pair.whole postcondition c) (fun _ => True) :=
  fun c hc => (oPair_whole_iff _ _ _).mpr ⟨base, trivial, fun _ => base_meets.2 c hc⟩

end AcornVerif.Intent.Postcondition
