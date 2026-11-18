/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.BigClass
import AcornVerif.Intent.PostconditionConsequences

/-!
# The consequences of the record of what makes a class of worlds big

Each consequence of `AcornVerif.Intent.BigClass.bigClass` stated here is proved to hold of the
record: what it requires of every trial that meets it, the trials it rules out, each beside `base`,
the trial that differs from it only where it attacks and meets the record, what the record still
allows, and how it stands to the postcondition's record.

Two things are not proved here, and each is a consequence for the owner's confirmation labelled
unproved, never a pass:

* The pair of this record with the postcondition's: that in every class which meets this record,
  and whose reward orders the compared agents as members solved do, some agent achieves the
  postcondition (`Served`). It is proved here of every two-door class with a fair aggregation and
  payment (`doors_served`) and of no other class; `AcornVerif.MissionVisits.retrace_mission` proves
  the postcondition of one agent on the classes of the kernel's worlds in visits that its exploring
  walks cover. A proof for every class needs an agent built for the class, and a class with finitely
  many actions to try.
* Condition (d) of the restatement, which this record does not carry.

That the record allows a trap, as condition (a) says it may, is proved: the class `pits` meets the
record (`pits_big`) and has an action, at the start of an attempt, after which a member's goal can
no longer be reached within the attempt (`pits_trap`, `trapsAllowed_holds`).

Two checks of lean-intent were not run, for the reasons the postcondition's consequences give: its
degenerate-subject and trivial-witness checks do not cover a subject that carries its own types
(rbeauchamp/lean-intent#43), and its cone exclusion has no implementation to run against. The
nearest degenerate subjects fail the record: a class that counts no member
(`hasCountedMember_holds`) and a class whose members are one world (`sameDoor_fails`).
-/

namespace AcornVerif.Intent.BigClass

open LeanIntent WorldInterface Postcondition

/-! ## The record reads the class only -/

/-- **The record reads the class, not its agent, its aggregation, its horizon or its lapses.** A
trial meets the record exactly when the trial with another agent, another way of aggregating
reward, another horizon and another number of lapses does. -/
theorem reads_class (w : Trial) (A : Agent w.Obs w.Act) (f : List Rat → Rat)
    (horizon lapses : Nat) :
    bigClass.Meets { w with agent := A, total := f, horizon := horizon, lapses := lapses } ↔
      bigClass.Meets w := by
  rw [bigClass_meets, bigClass_meets]
  exact Iff.rfl

/-! ## What the record requires -/

/-- **No agent that keeps nothing solves the whole class.** -/
def noFrozenAgentSolvesAll : Consequence Trial :=
  ⟨"no agent that keeps nothing of its experience solves every counted member on an attempt",
    .entailment, fun w =>
    ∀ B : Agent w.Obs w.Act, KeepsNothing B → ∀ n, w.solvedCount B n < w.counted.length⟩

theorem noFrozenAgentSolvesAll_holds : noFrozenAgentSolvesAll.HoldsOf bigClass :=
  fun _ hw B hB n =>
    let ⟨_, hk, h⟩ := (bigClass_meets.mp hw).2.2.1
    Nat.lt_of_le_of_lt (h B hB n) hk

/-- **The class counts at least one member.** -/
def hasCountedMember : Consequence Trial :=
  ⟨"the class counts at least one member", .entailment, fun w => w.counted ≠ []⟩

theorem hasCountedMember_holds : hasCountedMember.HoldsOf bigClass := by
  intro w hw he
  obtain ⟨k, hk, _⟩ := (bigClass_meets.mp hw).2.2.1
  rw [he] at hk
  exact Nat.not_lt_zero k hk

/-! ## Nobody does well on a first attempt -/

/-- The agent that takes, at each step, the action `A` takes at that step of its run in `R`. Its
memory counts its steps, so it keeps nothing of its experience. -/
def script {Obs Act : Type} (R : Member Obs Act) (A : Agent Obs Act) : Agent Obs Act where
  Memory := Nat
  initial := 0
  act := fun t _ => ((A.act (R.run A t).2 (given R A t)).1, t + 1)

theorem script_keepsNothing {Obs Act : Type} (R : Member Obs Act) (A : Agent Obs Act) :
    KeepsNothing (script R A) :=
  fun _ _ _ => rfl

/-- After `t` steps of its run in any member, a script has counted `t` steps. -/
theorem script_memory {Obs Act : Type} (R : Member Obs Act) (A : Agent Obs Act)
    (M : Member Obs Act) : ∀ t, (M.run (script R A) t).2 = t
  | 0 => rfl
  | t + 1 => congrArg (· + 1) (script_memory R A M t)

/-- Where a member gives `A` what `R` gives it until its goal is first met, then up to any time
before which no state of `A`'s run has met the goal, the script of `A`'s run in `R` is in the state
`A` is in, and `A` holds the memory it holds in `R`. -/
theorem script_follows {Obs Act : Type} (R M : Member Obs Act) (A : Agent Obs Act)
    (hM : ∀ t, (∀ u, u ≤ t → M.goal (M.run A u).1 = false) → given M A t = given R A t) :
    ∀ t, (∀ u, u < t → M.goal (M.run A u).1 = false) →
      (M.run (script R A) t).1 = (M.run A t).1 ∧ (M.run A t).2 = (R.run A t).2
  | 0, _ => ⟨rfl, rfl⟩
  | t + 1, h => by
    obtain ⟨ihs, ihm⟩ := script_follows R M A hM t (fun u hu => h u (Nat.lt_succ_of_lt hu))
    have hg : given M A t = given R A t := hM t (fun u hu => h u (Nat.lt_succ_of_le hu))
    have hmem := script_memory R A M t
    refine ⟨?_, ?_⟩
    · show M.step (M.run (script R A) t).1
          ((script R A).act (M.run (script R A) t).2
            (M.observe (M.run (script R A) t).1, M.reward (M.run (script R A) t).1)).1 =
        M.step (M.run A t).1 (A.act (M.run A t).2 (given M A t)).1
      rw [hmem, ihs, ihm, hg]
      rfl
    · show (A.act (M.run A t).2 (given M A t)).2 = (A.act (R.run A t).2 (given R A t)).2
      rw [ihm, hg]

/-- Where a member gives `A` what `R` gives it until its goal is first met, the script of `A`'s run
in `R` meets the member's goal no later than `A` does. -/
theorem script_meets {Obs Act : Type} (R M : Member Obs Act) (A : Agent Obs Act)
    (hM : ∀ t, (∀ u, u ≤ t → M.goal (M.run A u).1 = false) → given M A t = given R A t)
    (t : Nat) :
    M.goal (M.run A t).1 = true →
      ∃ t', t' ≤ t ∧ M.goal (M.run (script R A) t').1 = true := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro ht
    rcases Classical.em (∀ u, u < t → M.goal (M.run A u).1 = false) with hall | hall
    · exact ⟨t, Nat.le_refl t, by rw [(script_follows R M A hM t hall).1]; exact ht⟩
    · have hex : ∃ u, u < t ∧ M.goal (M.run A u).1 = true := by
        apply Classical.byContradiction
        intro hne
        apply hall
        intro u hu
        cases hgu : M.goal (M.run A u).1
        · rfl
        · exact absurd ⟨u, hu, hgu⟩ hne
      obtain ⟨u, hu, hgu⟩ := hex
      obtain ⟨t', ht', hg'⟩ := ih u hu hgu
      exact ⟨t', Nat.le_trans ht' (Nat.le_of_lt hu), hg'⟩

/-- An agent solves a member on its first attempt exactly when its run in the member is in a state
that meets the goal at some time before the attempt's length. -/
theorem solves_first_iff (w : Trial) (A : Agent w.Obs w.Act) (i : w.Index) :
    w.solves A i 0 = true ↔
      ∃ t, t < w.length ∧ (w.member i).goal (w.stateAt A i t) = true := by
  simp only [Trial.solves, Trial.attemptTimes, List.any_eq_true, List.mem_map, List.mem_range,
    Nat.mul_zero, Nat.zero_add]
  constructor
  · intro ⟨t, ⟨k, hk, hkt⟩, hg⟩
    exact ⟨t, hkt ▸ hk, hg⟩
  · intro ⟨t, ht, hg⟩
    exact ⟨t, ⟨t, ht, rfl⟩, hg⟩

/-- Where every element one test passes passes another, the first test passes no more elements of a
list than the second. -/
theorem filter_length_mono {α : Type} (p q : α → Bool) (h : ∀ x, p x = true → q x = true) :
    ∀ l : List α, (l.filter p).length ≤ (l.filter q).length
  | [] => Nat.le_refl _
  | x :: l => by
    have ih := filter_length_mono p q h l
    cases hp : p x
    · cases hq : q x <;> simp only [List.filter, hp, hq, List.length_cons] <;> omega
    · have hq := h x hp
      simp only [List.filter, hp, hq, List.length_cons]
      omega

/-- **Nobody does well on a first attempt.** In a class that conceals its goals and in which an
agent that keeps nothing of its experience solves only a small share, every agent, one that learns
included, solves on its first attempt at most the number of counted members that bounds that
share. -/
def firstAttemptSmall : Consequence Trial :=
  ⟨"on its first attempt, every agent solves at most a number of the counted members that is \
    smaller than their count", .entailment, fun w =>
    ∃ k, k < w.counted.length ∧ ∀ A : Agent w.Obs w.Act, w.solvedCount A 0 ≤ k⟩

theorem firstAttemptSmall_holds : firstAttemptSmall.HoldsOf bigClass := by
  intro w hw
  obtain ⟨_, ⟨R, hR⟩, ⟨k, hk, hfrozen⟩, _, _⟩ := bigClass_meets.mp hw
  refine ⟨k, hk, fun A => Nat.le_trans ?_ (hfrozen (script R A) (script_keepsNothing R A) 0)⟩
  show (w.counted.filter fun i => w.solves A i 0).length ≤
    (w.counted.filter fun i => w.solves (script R A) i 0).length
  apply filter_length_mono
  intro i hi
  obtain ⟨t, ht, hg⟩ := (solves_first_iff w A i).mp hi
  obtain ⟨t', ht', hg'⟩ := script_meets R (w.member i) A (fun t h => hR A i t h) t hg
  exact (solves_first_iff w (script R A) i).mpr ⟨t', Nat.lt_of_le_of_lt ht' ht, hg'⟩

/-! ## What the record rules out -/

theorem unreachable_fails : ¬ bigClass.Meets unreachable := fun h => by
  obtain ⟨acts, _, hg⟩ := (bigClass_meets.mp h).1 finder true 0
  have hf : false = true := hg
  exact Bool.noConfusion hf

/-- **A class with a goal that cannot be reached is ruled out**: the trial `unreachable`, whose
members have no state that meets a goal. Its neighbour is `base`. -/
def rulesOutUnreachableGoals : Consequence Trial :=
  ⟨"the trial unreachable, whose members' goals no state meets, is ruled out", .entailment,
    fun w => w ≠ unreachable⟩

theorem rulesOutUnreachableGoals_holds : rulesOutUnreachableGoals.HoldsOf bigClass :=
  fun _ hw he => unreachable_fails (he ▸ hw)

theorem revealing_fails : ¬ bigClass.Meets revealing := fun h => by
  obtain ⟨R, hR⟩ := (bigClass_meets.mp h).2.1
  have e := (hR finder true 0 (fun u hu => by cases Nat.le_zero.mp hu; rfl)).trans
    (hR finder false 0 (fun u hu => by cases Nat.le_zero.mp hu; rfl)).symm
  have e' : some true = some false := congrArg Prod.fst e
  exact absurd e' (by decide)

/-- **A class that shows which goal the agent faces is ruled out**: the trial `revealing`, whose
members show their door when they ask for one. Its neighbour is `base`. -/
def rulesOutShownGoals : Consequence Trial :=
  ⟨"the trial revealing, whose members show their door before it is tried, is ruled out",
    .entailment, fun w => w ≠ revealing⟩

theorem rulesOutShownGoals_holds : rulesOutShownGoals.HoldsOf bigClass :=
  fun _ hw he => revealing_fails (he ▸ hw)

theorem sameDoor_fails : ¬ bigClass.Meets sameDoor := fun h => by
  obtain ⟨k, hk, hf⟩ := (bigClass_meets.mp h).2.2.1
  have h2 : sameDoor.solvedCount (always true) 0 ≤ k :=
    hf (always true) (always_keepsNothing true) 0
  have hk' : k < 2 := hk
  have h3 : sameDoor.solvedCount (always true) 0 = 2 := by decide
  omega

/-- **A class that one fixed way of acting solves is ruled out**: the trial `sameDoor`, whose two
members have the same door. Its neighbour is `base`. -/
def rulesOutOneAnswer : Consequence Trial :=
  ⟨"the trial sameDoor, whose members are all solved by trying one door, is ruled out",
    .entailment, fun w => w ≠ sameDoor⟩

theorem rulesOutOneAnswer_holds : rulesOutOneAnswer.HoldsOf bigClass :=
  fun _ hw he => sameDoor_fails (he ▸ hw)

theorem hidden_fails : ¬ bigClass.Meets hidden := fun h => by
  obtain ⟨signal, hs⟩ := (bigClass_meets.mp h).2.2.2.1
  have h1 : signal (some false, 0) = true := hs (always true) true 1
  have h2 : signal (some false, 0) = false := hs (always true) false 1
  exact Bool.noConfusion (h1.symm.trans h2)

/-- **A class in which success does not show is ruled out**: the trial `hidden`, whose members pay
nothing and show the same thing whether the door tried was right or wrong. Its neighbour is
`base`. -/
def rulesOutHiddenSuccess : Consequence Trial :=
  ⟨"the trial hidden, whose members show and pay the same whether or not their goal is met, is \
    ruled out", .entailment, fun w => w ≠ hidden⟩

theorem rulesOutHiddenSuccess_holds : rulesOutHiddenSuccess.HoldsOf bigClass :=
  fun _ hw he => hidden_fails (he ▸ hw)

theorem stuck_fails : ¬ bigClass.Meets stuck := fun h => by
  have e : Door.miss = Door.ask := (bigClass_meets.mp h).2.2.2.2 finder true 1
  exact absurd e (by decide)

/-- **A class whose problems do not come back is ruled out**: the trial `stuck`, whose members
never ask for a door again after the first is tried. Its neighbour is `base`. -/
def rulesOutNoRecurrence : Consequence Trial :=
  ⟨"the trial stuck, whose members never return to the state they start in, is ruled out",
    .entailment, fun w => w ≠ stuck⟩

theorem rulesOutNoRecurrence_holds : rulesOutNoRecurrence.HoldsOf bigClass :=
  fun _ hw he => stuck_fails (he ▸ hw)

/-! ## What the record still allows -/

/-- **A class is big whatever its agent**: some trial that meets the record has an agent that keeps
nothing of its experience. With condition (d) left to a later subject, nothing in this record reads
the agent. -/
def agentMayKeepNothing : Consequence Trial :=
  ⟨"a class may meet these conditions whatever its agent, even one that keeps nothing of its \
    experience", .possibility, fun w => KeepsNothing w.agent⟩

theorem agentMayKeepNothing_holds : agentMayKeepNothing.HoldsOf bigClass :=
  ⟨fixed, doors_big List.sum 1 (always true), always_keepsNothing true⟩

/-! ## A class with a trap -/

/-- The states of a member of the class with a trap. -/
inductive Pit where
  /-- The world asks for a door. -/
  | ask
  /-- The door just tried was the member's. -/
  | hit
  /-- The door just tried was not the member's: the pit. -/
  | fell
  /-- The attempt's last step, whichever door was tried. -/
  | over
  deriving DecidableEq

/-- The member of the class with a trap whose door is `b`. Asked for a door, it moves to `hit` when
the door tried is `b` and to the pit, `fell`, otherwise, and shows which. Whatever the next action,
it then moves to `over`, and from there asks again. It generates the reward 1 at `hit` and none
elsewhere, and its goal is `hit`. -/
def pit (b : Bool) : Member (Option Bool) Bool where
  State := Pit
  start := .ask
  observe := fun
    | .ask => none
    | .hit => some true
    | _ => some false
  reward := fun
    | .hit => 1
    | _ => 0
  step := fun
    | .ask, a => bif a == b then .hit else .fell
    | .over, _ => .ask
    | _, _ => .over
  goal := fun
    | .hit => true
    | _ => false

/-- The class with a trap: one member for each door, both counted, and attempts of three steps, one
to try a door, one in which nothing the agent does matters, and one before the member asks again.
Its rewards are summed, its promises are read over its first three attempts with no lapse, and its
agent is `finder`; the record reads none of those four (`reads_class`). -/
def pits : Trial where
  Obs := Option Bool
  Act := Bool
  Index := Bool
  member := pit
  counted := [true, false]
  length := 3
  total := List.sum
  horizon := 3
  lapses := 0
  agent := finder

/-- A world that asks for a door and never has one: whatever door is tried it moves to the pit,
then to `over`, and asks again. It generates no reward and has no goal. -/
def pitWall : Member (Option Bool) Bool where
  State := Pit
  start := .ask
  observe := fun
    | .ask => none
    | .hit => some true
    | _ => some false
  reward := fun _ => 0
  step := fun
    | .ask, _ => .fell
    | .over, _ => .ask
    | _, _ => .over
  goal := fun _ => false

/-- Three steps after it asks for a door, a member of the class with a trap asks again. -/
theorem pit_restart (b a a' a'' : Bool) :
    (pit b).step ((pit b).step ((pit b).step Pit.ask a) a') a'' = Pit.ask := by
  cases a <;> cases b <;> rfl

/-- Every attempt of every agent's run in a member of the class with a trap starts with the member
asking for a door. -/
theorem pit_ask (b : Bool) (A : Agent (Option Bool) Bool) :
    ∀ n, ((pit b).run A (3 * n)).1 = Pit.ask
  | 0 => rfl
  | n + 1 => by
    have h := pit_ask b A n
    show (pit b).step ((pit b).step ((pit b).step ((pit b).run A (3 * n)).1 _) _) _ = Pit.ask
    rw [h]
    exact pit_restart b _ _ _

/-- From a state that does not meet a member's goal, a step that does not reach it either is the
step `pitWall` takes. -/
theorem pit_next_wall (b : Bool) (A : Agent (Option Bool) Bool) (c : Pit × A.Memory)
    (h : (pit b).goal c.1 = false) (h' : (pit b).goal ((pit b).next A c).1 = false) :
    (pit b).next A c = pitWall.next A c := by
  obtain ⟨s, m⟩ := c
  cases s with
  | ask =>
    have hg : (pit b).goal
        (bif (A.act m (none, 0)).1 == b then Pit.hit else Pit.fell) = false := h'
    show ((bif (A.act m (none, 0)).1 == b then Pit.hit else Pit.fell), (A.act m (none, 0)).2) =
      (Pit.fell, (A.act m (none, 0)).2)
    cases hab : (A.act m (none, 0)).1 == b
    · rfl
    · rw [hab] at hg
      have hf : true = false := hg
      exact Bool.noConfusion hf
  | hit =>
    have hf : true = false := h
    exact Bool.noConfusion hf
  | fell => rfl
  | over => rfl

/-- Up to any time before which no state has met a member's goal, an agent's run in that member of
the class with a trap is its run in `pitWall`. -/
theorem pit_run_wall (b : Bool) (A : Agent (Option Bool) Bool) :
    ∀ t, (∀ u, u ≤ t → (pit b).goal ((pit b).run A u).1 = false) →
      (pit b).run A t = pitWall.run A t
  | 0, _ => rfl
  | t + 1, h => by
    have ih := pit_run_wall b A t (fun u hu => h u (Nat.le_succ_of_le hu))
    show (pit b).next A ((pit b).run A t) = pitWall.next A (pitWall.run A t)
    rw [← ih]
    exact pit_next_wall b A _ (h t (Nat.le_succ t)) (h (t + 1) (Nat.le_refl _))

/-- The door the agent `A` tries on attempt `n` of its run in the member `b` of the class with a
trap: its action at the attempt's first step. -/
def pitTried (A : Agent (Option Bool) Bool) (b : Bool) (n : Nat) : Bool :=
  (A.act ((pit b).run A (3 * n)).2
    ((pit b).observe ((pit b).run A (3 * n)).1, (pit b).reward ((pit b).run A (3 * n)).1)).1

/-- An agent solves a member of the class with a trap on an attempt exactly when the door it tries
is the member's. -/
theorem pits_solves (A : Agent (Option Bool) Bool) (b : Bool) (n : Nat) :
    pits.solves A b n = (pitTried A b n == b) := by
  have h1 : ((pit b).run A (3 * n + 1)).1 =
      bif pitTried A b n == b then Pit.hit else Pit.fell := by
    show (pit b).step ((pit b).run A (3 * n)).1 (pitTried A b n) = _
    rw [pit_ask]
    rfl
  have h2 : ((pit b).run A (3 * n + 2)).1 = Pit.over := by
    show (pit b).step ((pit b).run A (3 * n + 1)).1 _ = _
    rw [h1]
    cases pitTried A b n == b <;> rfl
  show ((pit b).goal ((pit b).run A (3 * n)).1 ||
    ((pit b).goal ((pit b).run A (3 * n + 1)).1 ||
      ((pit b).goal ((pit b).run A (3 * n + 2)).1 || false))) = _
  rw [h1, h2, pit_ask]
  cases pitTried A b n == b <;> rfl

/-- An agent that keeps nothing of its experience tries the same door in both members of the class
with a trap on each attempt. -/
theorem keepsNothing_pitTried {B : Agent (Option Bool) Bool} (h : KeepsNothing B) (b : Bool)
    (n : Nat) : pitTried B b n = (B.act (drift B (none, 0) (3 * n)) (none, 0)).1 := by
  unfold pitTried
  rw [pit_ask, keepsNothing_memory h (pit b) (none, 0)]
  rfl

theorem pits_goalsReachable : goalsReachable.holds pits :=
  fun (A : Agent (Option Bool) Bool) (b : Bool) n => ⟨[b], (by decide : 1 < 3), by
    show (pit b).goal (afterActions (pit b) ((pit b).run A (3 * n)).1 [b]) = true
    rw [pit_ask]
    cases b <;> rfl⟩

theorem pits_goalsConcealed : goalsConcealed.holds pits :=
  ⟨pitWall, fun (A : Agent (Option Bool) Bool) (b : Bool) t h => by
    have hs : (pit b).goal ((pit b).run A t).1 = false := h t (Nat.le_refl t)
    show ((pit b).observe ((pit b).run A t).1, (pit b).reward ((pit b).run A t).1) =
        (pitWall.observe (pitWall.run A t).1, pitWall.reward (pitWall.run A t).1)
    rw [← pit_run_wall b A t h]
    generalize ((pit b).run A t).1 = s at hs
    cases s with
    | ask => rfl
    | hit =>
      have hf : true = false := hs
      exact Bool.noConfusion hf
    | fell => rfl
    | over => rfl⟩

/-- How many members of the class with a trap an agent solves on an attempt. -/
theorem pits_solvedCount (A : Agent (Option Bool) Bool) (n : Nat) :
    pits.solvedCount A n = tally (pits.solves A true n) (pits.solves A false n) := by
  show ([true, false].filter fun i => pits.solves A i n).length = _
  cases h1 : pits.solves A true n <;>
    cases h2 : pits.solves A false n <;> simp only [List.filter, h1, h2] <;> rfl

theorem pits_frozenShareSmall : frozenShareSmall.holds pits :=
  ⟨1, Nat.lt_succ_self 1, fun (B : Agent (Option Bool) Bool) hB n => by
    rw [pits_solvedCount, pits_solves, pits_solves, keepsNothing_pitTried hB,
      keepsNothing_pitTried hB]
    cases (B.act (drift B (none, 0) (3 * n)) (none, 0)).1 <;> decide⟩

theorem pits_successShows : successShows.holds pits :=
  ⟨fun (o : Option Bool × Rat) => o.1 == some true,
    fun (A : Agent (Option Bool) Bool) (b : Bool) t => by
    show ((pit b).observe ((pit b).run A t).1 == some true) = (pit b).goal ((pit b).run A t).1
    generalize ((pit b).run A t).1 = s
    cases s <;> rfl⟩

theorem pits_attemptsRecur : attemptsRecur.holds pits :=
  fun (A : Agent (Option Bool) Bool) (b : Bool) n => pit_ask b A n

/-- **The class with a trap meets the record.** -/
theorem pits_big : bigClass.Meets pits :=
  bigClass_meets.mpr ⟨pits_goalsReachable, pits_goalsConcealed, pits_frozenShareSmall,
    pits_successShows, pits_attemptsRecur⟩

/-- A class has a trap when some member has an action, at the start of an attempt, that leads
somewhere its goal can no longer be reached within the attempt, and not for want of time: no
actions that fit in the rest of the attempt reach the goal from where that action leads, though as
few actions reach it from the member's start. -/
def HasTrap (w : Trial) : Prop :=
  ∃ (i : w.Index) (a : w.Act),
    (∃ acts : List w.Act, acts.length + 1 < w.length ∧
      (w.member i).goal (afterActions (w.member i) (w.member i).start acts) = true) ∧
    ∀ acts : List w.Act, acts.length + 1 < w.length →
      (w.member i).goal
        (afterActions (w.member i) ((w.member i).step (w.member i).start a) acts) = false

/-- In the class with a trap, the wrong door at the start of an attempt is a trap: from the pit no
action reaches the goal in the step that remains, though one action reaches it from the start. -/
theorem pits_trap : HasTrap pits :=
  ⟨true, false, ⟨[true], (by decide : 2 < 3), rfl⟩, fun acts h =>
    match acts, h with
    | [], _ => rfl
    | [_], _ => rfl
    | _ :: _ :: rest, h => absurd h (by show ¬ (rest.length + 1 + 1 + 1 < 3); omega)⟩

/-- **Reachable goals do not rule out traps**, as condition (a) says: some trial that meets the
record has a trap. -/
def trapsAllowed : Consequence Trial :=
  ⟨"a class may have a trap: an action at the start of an attempt after which the member's goal \
    can no longer be reached within the attempt, though as few actions as remain reach it from \
    the member's start", .possibility, HasTrap⟩

theorem trapsAllowed_holds : trapsAllowed.HoldsOf bigClass :=
  ⟨pits, pits_big, pits_trap⟩

/-! ## This record and the postcondition's -/

/-- **The postcondition already asks for condition (c).** A trial that meets the postcondition's
record has an agent that solves, on some attempt, more counted members than any agent that keeps
nothing of its experience solves on any attempt, so such an agent never solves them all. -/
theorem frozenShareSmall_of_postcondition {w : Trial} (h : postcondition.Meets w) :
    frozenShareSmall.holds w := by
  obtain ⟨n, -, hn⟩ := solvesMoreInTime_holds w h
  have hle : w.solvedCount w.agent n ≤ w.counted.length := List.length_filter_le _ _
  have hpos := hn (shell w.agent) (shell_keepsNothing _) 0
  refine ⟨w.solvedCount w.agent n - 1, by omega, fun B hB k => ?_⟩
  have hlt := hn B hB k
  omega

/-- In a class that meets this record, every two attempts of a member start from the same state in
the agent's run. -/
theorem sameProblem_of_big {w : Trial} (hb : bigClass.Meets w) (i : w.Index) (n k : Nat) :
    w.SameProblem i n k :=
  ((bigClass_meets.mp hb).2.2.2.2 w.agent i k).trans
    ((bigClass_meets.mp hb).2.2.2.2 w.agent i n).symm

/-- **In a big class the postcondition's retention is asked without condition on the member's
attempts.** In a class that meets this record, an agent that keeps solving in the postcondition's
sense has, for each member, at most the class's number of lapses, outside which it solves the
member on every attempt before the class's horizon that follows one on which it solved it. -/
theorem retention_unconditional {w : Trial} (hb : bigClass.Meets w) (hk : keepsSolving.holds w)
    (i : w.Index) :
    ∃ lapsed : List Nat, lapsed.length ≤ w.lapses ∧ ∀ n n', n ≤ n' → n' < w.horizon →
      w.solves w.agent i n = true → n' ∉ lapsed → w.solves w.agent i n' = true := by
  obtain ⟨lapsed, few, keeps⟩ := hk i
  exact ⟨lapsed, few, fun n n' hle before hs out =>
    keeps n n' hle before (fun k _ _ => sameProblem_of_big hb i n k) hs out⟩

/-- **In a big class the members solved on the attempt of the advantage are solved again.** In a
class that meets this record, an agent that meets the postcondition's record earns its advantage
on an attempt each of whose solved members it solves again on a later attempt before the
horizon. So in such a class no agent meets the postcondition by an advantage it earns once and
never follows. -/
theorem advantage_solved_again {w : Trial} (hb : bigClass.Meets w)
    (hp : postcondition.Meets w) :
    ∃ n, (∀ B, KeepsNothing B → ∀ k, w.classReward B k < w.classReward w.agent n) ∧
      ∀ i, w.solves w.agent i n = true →
        ∃ n', n < n' ∧ n' < w.horizon ∧ w.solves w.agent i n' = true := by
  obtain ⟨n, more, again⟩ := advantageSolvedAgain_holds w hp
  exact ⟨n, more, fun i solved => again i solved fun k _ => sameProblem_of_big hb i n k⟩

/-- Some agent achieves the postcondition in the class of the trial `w`: the trial with that agent
in place of its own meets the postcondition's record. -/
def Served (w : Trial) : Prop :=
  ∃ A : Agent w.Obs w.Act, postcondition.Meets { w with agent := A }

/-- **Every two-door class with a fair aggregation and payment is served**, by `finder`. -/
theorem doors_served (total : List Rat → Rat) (pay : Rat) (X : Agent (Option Bool) Bool)
    (h : Fair total pay) : Served (doors total pay X) :=
  ⟨finder, doors_finder_meets total pay h⟩

end AcornVerif.Intent.BigClass
