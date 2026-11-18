/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.BigClassBlindCompare

/-!
# The blind cases reading of contract 2, and the record's verdict on each case

PROVISIONAL HEADER
-/

namespace AcornVerif.Intent.BigClass.Cases

open LeanIntent WorldInterface Postcondition
open BigClassBlind (ClassWithAgent)
open Compare (shown ruleAgent ruleAgent_keepsNothing)

/-! ## From a case to a trial -/

/-- The trial of a class with an agent that counts the members `counted`. A case gives a class with
an agent and says nothing of which members are counted, so each verdict below is proved for every
list of counted members. The trial sums an attempt's rewards and has horizon and lapses 0; the
record reads none of the three (`reads_class`). -/
def counting (c : ClassWithAgent) (counted : List c.Index) : Trial where
  Obs := c.Obs
  Act := c.Act
  Index := c.Index
  member := c.member
  counted := counted
  length := c.length
  total := List.sum
  horizon := 0
  lapses := 0
  agent := c.agent

/-- What the blind sessions were given of the trial of a case is the case. -/
theorem shown_counting (c : ClassWithAgent) (counted : List c.Index) :
    shown (counting c counted) = c :=
  rfl

/-- Where an attempt lasts at most one step and a member's start does not meet its goal, the
record's condition (a) fails: it asks for a list of fewer actions than an attempt has steps. -/
theorem unreachable_of_short (w : Trial) (i : w.Index) (hlen : w.length ≤ 1)
    (hstart : (w.member i).goal (w.member i).start = false) : ¬ goalsReachable.holds w := by
  intro h
  obtain ⟨acts, hl, hg⟩ := h w.agent i 0
  match acts, hl, hg with
  | [], _, hg =>
    have hf : (w.member i).goal (w.member i).start = true := hg
    rw [hstart] at hf
    exact Bool.noConfusion hf
  | _ :: rest, hl, _ =>
    have hl' : rest.length + 1 < w.length := hl
    omega

/-- Where an attempt lasts no step, the record's condition (a) fails of any class with a member,
even one whose start meets its goal: no list has fewer actions than none. -/
theorem unreachable_of_zero (w : Trial) (i : w.Index) (hlen : w.length = 0) :
    ¬ goalsReachable.holds w := by
  intro h
  obtain ⟨acts, hl, _⟩ := h w.agent i 0
  omega

/-- Where an attempt lasts no step, no agent solves any member on any attempt, in the record's
sense: an attempt of no step has no time at which a goal could be met. -/
theorem solves_of_zero (w : Trial) (hlen : w.length = 0) (A : Agent w.Obs w.Act) (i : w.Index)
    (n : Nat) : w.solves A i n = false := by
  cases hs : w.solves A i n
  · rfl
  · obtain ⟨j, hj, _⟩ := (solves_iff w A i n).mp hs
    omega

/-! ## Table worlds: the members of cases 1 to 10 and 13 -/

/-- A state of a table world: the context, from 0 through 99, the time within it, from 0 through
999,999,999, and whether the last action was the answer. -/
abbrev Cell : Type := Fin 100 × Fin 1000000000 × Bool

/-- What a table world shows: an integer from 0 through 199 and a flag, `true` for `begin` and
`false` for `inside`. -/
abbrev Sight : Type := Fin 200 × Bool

/-- One step of a table world whose answers are `hit`: the time increases by one, wrapping to zero
at 999,999,999, where the context moves on by one, modulo 100; and the next state says whether the
action was the answer of the context it was taken in. -/
def advance {Act : Type} (hit : Fin 100 → Act → Bool) (s : Cell) (a : Act) : Cell :=
  (if s.2.1.val = 999999999 then s.1 + 1 else s.1, s.2.1 + 1, hit s.1 a)

/-- The table world with the answers `hit`, the observation `observe` and the reward `reward`: it
starts in the context 0 at the time 0, and its goal is met exactly where the last action was the
answer. -/
def table {Act : Type} (hit : Fin 100 → Act → Bool) (observe : Cell → Sight)
    (reward : Cell → Rat) : Member Sight Act where
  State := Cell
  start := (0, 0, false)
  observe := observe
  reward := reward
  step := advance hit
  goal := fun s => s.2.2

/-- The class of table worlds with one member for each key, attempts of `length` steps and the
agent `agent`. -/
def tables {Key Act : Type} (hit : Key → Fin 100 → Act → Bool) (observe : Key → Cell → Sight)
    (reward : Key → Cell → Rat) (length : Nat) (agent : Agent Sight Act) : ClassWithAgent where
  Obs := Sight
  Act := Act
  Index := Key
  member := fun k => table (hit k) (observe k) (reward k)
  length := length
  agent := agent

section Tables

variable {Key Act : Type} (hit : Key → Fin 100 → Act → Bool) (observe : Key → Cell → Sight)
  (reward : Key → Cell → Rat) (agent : Agent Sight Act)

/-- The record's condition (a) fails of a class of table worlds with attempts of one step: a
member's start does not meet its goal, and an attempt of one step leaves room for no action. -/
theorem tables_unreachable (k : Key) (counted : List Key) :
    ¬ goalsReachable.holds (counting (tables hit observe reward 1 agent) counted) :=
  unreachable_of_short _ k (Nat.le_refl 1) rfl

/-- The attempts of a class of table worlds with attempts of one step do not recur: after one step
a member's time is 1, not 0. -/
theorem tables_not_recur (k : Key) (counted : List Key) :
    ¬ attemptsRecur.holds (counting (tables hit observe reward 1 agent) counted) := fun h => by
  have e : (0 : Fin 1000000000) + 1 = 0 := congrArg (fun s : Cell => s.2.1) (h agent k 1)
  exact absurd e (by decide)

/-- Where one reading of what a table world gives says whether the last action was the answer,
success shows, in the record's sense. -/
theorem tables_success (signal : Sight × Rat → Bool)
    (h : ∀ k s, signal (observe k s, reward k s) = s.2.2) (length : Nat) (counted : List Key) :
    successShows.holds (counting (tables hit observe reward length agent) counted) :=
  ⟨signal, fun (A : Agent Sight Act) k t =>
    h k ((table (hit k) (observe k) (reward k)).run A t).1⟩

/-- Where the members of a class of table worlds show and pay the same at every state whose last
action was not the answer, an agent's run in a member is, up to any time before which no state has
met the goal, its run in the table world with no answer. -/
theorem tables_run (observe₀ : Cell → Sight) (reward₀ : Cell → Rat)
    (h : ∀ k s, s.2.2 = false → observe k s = observe₀ s ∧ reward k s = reward₀ s) (k : Key)
    (A : Agent Sight Act) :
    ∀ t, (∀ u, u ≤ t → ((table (hit k) (observe k) (reward k)).run A u).1.2.2 = false) →
      (table (hit k) (observe k) (reward k)).run A t =
        (table (fun _ _ => false) observe₀ reward₀).run A t
  | 0, _ => rfl
  | t + 1, hg => by
    have ih := tables_run observe₀ reward₀ h k A t (fun u hu => hg u (Nat.le_succ_of_le hu))
    have h0 : ((table (hit k) (observe k) (reward k)).run A t).1.2.2 = false :=
      hg t (Nat.le_succ t)
    have h1 : ((table (hit k) (observe k) (reward k)).next A
        ((table (hit k) (observe k) (reward k)).run A t)).1.2.2 = false :=
      hg (t + 1) (Nat.le_refl _)
    show (table (hit k) (observe k) (reward k)).next A
        ((table (hit k) (observe k) (reward k)).run A t) =
      (table (fun _ _ => false) observe₀ reward₀).next A
        ((table (fun _ _ => false) observe₀ reward₀).run A t)
    rw [← ih]
    generalize (table (hit k) (observe k) (reward k)).run A t = p at h0 h1
    obtain ⟨s, m⟩ := p
    obtain ⟨ho, hr⟩ := h k s h0
    have h1' : hit k s.1 (A.act m (observe k s, reward k s)).1 = false := h1
    show (advance (hit k) s (A.act m (observe k s, reward k s)).1,
        (A.act m (observe k s, reward k s)).2) =
      (advance (fun _ _ => false) s (A.act m (observe₀ s, reward₀ s)).1,
        (A.act m (observe₀ s, reward₀ s)).2)
    rw [ho, hr] at h1' ⊢
    show ((if s.2.1.val = 999999999 then s.1 + 1 else s.1, s.2.1 + 1,
        hit k s.1 (A.act m (observe₀ s, reward₀ s)).1), _) = _
    rw [h1']
    rfl

/-- **Where the members of a class of table worlds show and pay the same at every state whose last
action was not the answer, the class conceals its goals**, in the record's sense: the reference
world is the table world with no answer. -/
theorem tables_concealed (observe₀ : Cell → Sight) (reward₀ : Cell → Rat)
    (h : ∀ k s, s.2.2 = false → observe k s = observe₀ s ∧ reward k s = reward₀ s)
    (length : Nat) (counted : List Key) :
    goalsConcealed.holds (counting (tables hit observe reward length agent) counted) :=
  ⟨table (fun _ _ => false) observe₀ reward₀, fun (A : Agent Sight Act) k t hg => by
    have hrun := tables_run hit observe reward observe₀ reward₀ h k A t hg
    have h0 : ((table (hit k) (observe k) (reward k)).run A t).1.2.2 = false :=
      hg t (Nat.le_refl t)
    obtain ⟨ho, hr⟩ := h k _ h0
    show (observe k ((table (hit k) (observe k) (reward k)).run A t).1,
        reward k ((table (hit k) (observe k) (reward k)).run A t).1) =
      (observe₀ ((table (fun _ _ => false) observe₀ reward₀).run A t).1,
        reward₀ ((table (fun _ _ => false) observe₀ reward₀).run A t).1)
    rw [ho, hr, hrun]⟩

end Tables

/-- What a table world ordinarily shows: its context, and `begin` exactly at the time 0. -/
def sight (s : Cell) : Sight := (Fin.ofNat 200 s.1.val, decide (s.2.1 = 0))

/-- What a table world ordinarily pays: 1 where the last action was the answer and 0 elsewhere. -/
def pay (s : Cell) : Rat := if s.2.2 then 1 else 0

/-- The ordinary reward is 1 exactly where the last action was the answer. -/
theorem pay_shows (s : Cell) : decide (pay s = 1) = s.2.2 := by
  obtain ⟨c, t, b⟩ := s
  cases b
  · show decide ((0 : Rat) = 1) = false
    decide
  · show decide ((1 : Rat) = 1) = true
    decide

/-- The answers of a table world over `n` buttons: the button of each of its 100 contexts. -/
abbrev Answers (n : Nat) : Type := Fin 100 → Fin n

/-- The agent of most cases, over `n` buttons. It ignores the observation's integer. On `begin` it
outputs the button 0; on `inside` it outputs its memory when the reward is 1 or -7, and its memory
plus one, modulo `n`, for every other reward. Its next memory is the button it outputs. -/
def searcher (n : Nat) [NeZero n] : Agent Sight (Fin n) where
  Memory := Fin n
  initial := 0
  act := fun m o =>
    if o.1.2 then (0, 0) else if o.2 = 1 ∨ o.2 = -7 then (m, m) else (m + 1, m + 1)

/-- Case 1, which the cases reading judges big: 100 independent answers among 1,000,000 buttons,
each lasting 1,000,000,000 steps, attempts of one step, and an agent with memory for one answer. -/
def case1 : ClassWithAgent :=
  tables (fun (k : Answers 1000000) c a => a == k c) (fun _ => sight) (fun _ => pay) 1
    (searcher 1000000)

/-- The agent of case 2: its memory is a button for each context and, if any, the context and the
button it last tried. On each step it first writes into the pending context's entry the pending
button, when the reward is 1 or -7, or that button plus one otherwise; it then outputs the entry of
the context shown, taken modulo 100, and keeps that context and button as pending. -/
def keeper : Agent Sight (Fin 1000000) where
  Memory := (Fin 100 → Fin 1000000) × Option (Fin 100 × Fin 1000000)
  initial := (fun _ => 0, none)
  act := fun m o =>
    let entries : Fin 100 → Fin 1000000 :=
      match m.2 with
      | none => m.1
      | some (c, b) =>
        fun c' => if c' = c then (if o.2 = 1 ∨ o.2 = -7 then b else b + 1) else m.1 c'
    (entries (Fin.ofNat 100 o.1.1.val),
      (entries, some (Fin.ofNat 100 o.1.1.val, entries (Fin.ofNat 100 o.1.1.val))))

/-- Case 2: the class of case 1 with an agent whose memory holds the whole table of answers. -/
def case2 : ClassWithAgent :=
  tables (fun (k : Answers 1000000) c a => a == k c) (fun _ => sight) (fun _ => pay) 1 keeper

/-- Case 3: the class of case 1 with one independent answer, that of the context 0, in every
context. -/
def case3 : ClassWithAgent :=
  tables (fun (k : Answers 1000000) _ a => a == k 0) (fun _ => sight) (fun _ => pay) 1
    (searcher 1000000)

/-- Case 4: the class of case 1 over two buttons. -/
def case4 : ClassWithAgent :=
  tables (fun (k : Answers 2) c a => a == k c) (fun _ => sight) (fun _ => pay) 1 (searcher 2)

/-- Case 5: the class of case 1 over twenty buttons. -/
def case5 : ClassWithAgent :=
  tables (fun (k : Answers 20) c a => a == k c) (fun _ => sight) (fun _ => pay) 1 (searcher 20)

/-- Case 6: the class of case 1 whose reward, where the last action was not the answer, is -1 when
the current answer is even and -2 when it is odd. -/
def case6 : ClassWithAgent :=
  tables (fun (k : Answers 1000000) c a => a == k c) (fun _ => sight)
    (fun k s => if s.2.2 then 1 else if (k s.1).val % 2 = 0 then -1 else -2) 1 (searcher 1000000)

/-- Case 7: the class of case 1 whose observation adds 100 to its integer when the current answer
is odd, at every state after the time 0 whose last action was not the answer. -/
def case7 : ClassWithAgent :=
  tables (fun (k : Answers 1000000) c a => a == k c)
    (fun k s =>
      (if s.2.1 ≠ 0 ∧ s.2.2 = false then Fin.ofNat 200 (s.1.val + 100 * ((k s.1).val % 2))
        else Fin.ofNat 200 s.1.val, decide (s.2.1 = 0)))
    (fun _ => pay) 1 (searcher 1000000)

/-- Case 8: the class of case 1 whose observation adds 100 to its integer when the current answer
is odd, at the states whose last action was the answer. -/
def case8 : ClassWithAgent :=
  tables (fun (k : Answers 1000000) c a => a == k c)
    (fun k s =>
      (if s.2.2 then Fin.ofNat 200 (s.1.val + 100 * ((k s.1).val % 2))
        else Fin.ofNat 200 s.1.val, decide (s.2.1 = 0)))
    (fun _ => pay) 1 (searcher 1000000)

/-- Case 9: the class of case 1 with the reward 0 everywhere. -/
def case9 : ClassWithAgent :=
  tables (fun (k : Answers 1000000) c a => a == k c) (fun _ => sight) (fun _ _ => 0) 1
    (searcher 1000000)

/-- Case 10: the class of case 1 with the reward -7 where the last action was the answer and 0
elsewhere. -/
def case10 : ClassWithAgent :=
  tables (fun (k : Answers 1000000) c a => a == k c) (fun _ => sight)
    (fun _ s => if s.2.2 then -7 else 0) 1 (searcher 1000000)

/-- Case 13: the class of case 1 with an agent of one memory that always outputs the button 0. -/
def case13 : ClassWithAgent :=
  tables (fun (k : Answers 1000000) c a => a == k c) (fun _ => sight) (fun _ => pay) 1
    (always 0)

/-! ## The record's verdicts on cases 1 to 10 and 13

Each theorem holds whichever members the trial counts. On each of these cases the record's
condition (a) fails and its attempts do not recur: the case's attempts last one step, which leaves
room for no action, and its worlds never return to their start. So the record is not met.
Condition (c) is decided here for case 4 alone; on the other cases it depends on which members are
counted, which a case does not say. -/

/-- Case 1. The cases reading: every condition met, big. The record: (a) fails; (b) holds; success
shows; the attempts do not recur; not met. -/
theorem c1 (counted : List (Answers 1000000)) :
    ¬ goalsReachable.holds (counting case1 counted) ∧
      goalsConcealed.holds (counting case1 counted) ∧
      successShows.holds (counting case1 counted) ∧
      ¬ attemptsRecur.holds (counting case1 counted) ∧
      ¬ bigClass.Meets (counting case1 counted) :=
  ⟨tables_unreachable _ _ _ _ (fun _ => 0) counted,
    tables_concealed _ _ _ _ sight pay (fun _ _ _ => ⟨rfl, rfl⟩) 1 counted,
    tables_success _ _ _ _ (fun o => decide (o.2 = 1)) (fun _ s => pay_shows s) 1 counted,
    tables_not_recur _ _ _ _ (fun _ => 0) counted,
    fun h => tables_unreachable _ _ _ _ (fun _ => 0) counted (bigClass_meets.mp h).1⟩

/-- Case 2. The cases reading: (a) to (c) met, (d) not met, both parts of sentence 6 met, not big.
The record: (a) fails; (b) holds; success shows; the attempts do not recur; not met. -/
theorem c2 (counted : List (Answers 1000000)) :
    ¬ goalsReachable.holds (counting case2 counted) ∧
      goalsConcealed.holds (counting case2 counted) ∧
      successShows.holds (counting case2 counted) ∧
      ¬ attemptsRecur.holds (counting case2 counted) ∧
      ¬ bigClass.Meets (counting case2 counted) :=
  ⟨tables_unreachable _ _ _ _ (fun _ => 0) counted,
    tables_concealed _ _ _ _ sight pay (fun _ _ _ => ⟨rfl, rfl⟩) 1 counted,
    tables_success _ _ _ _ (fun o => decide (o.2 = 1)) (fun _ s => pay_shows s) 1 counted,
    tables_not_recur _ _ _ _ (fun _ => 0) counted,
    fun h => tables_unreachable _ _ _ _ (fun _ => 0) counted (bigClass_meets.mp h).1⟩

/-- Case 3. The cases reading: (a) to (c) met, (d) not met, both parts of sentence 6 met, not big.
The record: (a) fails; (b) holds; success shows; the attempts do not recur; not met. -/
theorem c3 (counted : List (Answers 1000000)) :
    ¬ goalsReachable.holds (counting case3 counted) ∧
      goalsConcealed.holds (counting case3 counted) ∧
      successShows.holds (counting case3 counted) ∧
      ¬ attemptsRecur.holds (counting case3 counted) ∧
      ¬ bigClass.Meets (counting case3 counted) :=
  ⟨tables_unreachable _ _ _ _ (fun _ => 0) counted,
    tables_concealed _ _ _ _ sight pay (fun _ _ _ => ⟨rfl, rfl⟩) 1 counted,
    tables_success _ _ _ _ (fun o => decide (o.2 = 1)) (fun _ s => pay_shows s) 1 counted,
    tables_not_recur _ _ _ _ (fun _ => 0) counted,
    fun h => tables_unreachable _ _ _ _ (fun _ => 0) counted (bigClass_meets.mp h).1⟩

/-- Case 5. The cases reading: (a), (b) and (d) met, (c) not settled, both parts of sentence 6 met,
overall not settled. The record: (a) fails; (b) holds; success shows; the attempts do not recur;
not met. -/
theorem c5 (counted : List (Answers 20)) :
    ¬ goalsReachable.holds (counting case5 counted) ∧
      goalsConcealed.holds (counting case5 counted) ∧
      successShows.holds (counting case5 counted) ∧
      ¬ attemptsRecur.holds (counting case5 counted) ∧
      ¬ bigClass.Meets (counting case5 counted) :=
  ⟨tables_unreachable _ _ _ _ (fun _ => 0) counted,
    tables_concealed _ _ _ _ sight pay (fun _ _ _ => ⟨rfl, rfl⟩) 1 counted,
    tables_success _ _ _ _ (fun o => decide (o.2 = 1)) (fun _ s => pay_shows s) 1 counted,
    tables_not_recur _ _ _ _ (fun _ => 0) counted,
    fun h => tables_unreachable _ _ _ _ (fun _ => 0) counted (bigClass_meets.mp h).1⟩

/-- Case 13. The cases reading: (a) to (d) met, the success signal met, temporal coherence not met,
since the agent has no memory to learn with, not big. The record, which reads no agent: (a) fails;
(b) holds; success shows; the attempts do not recur; not met. -/
theorem c13 (counted : List (Answers 1000000)) :
    ¬ goalsReachable.holds (counting case13 counted) ∧
      goalsConcealed.holds (counting case13 counted) ∧
      successShows.holds (counting case13 counted) ∧
      ¬ attemptsRecur.holds (counting case13 counted) ∧
      ¬ bigClass.Meets (counting case13 counted) :=
  ⟨tables_unreachable _ _ _ _ (fun _ => 0) counted,
    tables_concealed _ _ _ _ sight pay (fun _ _ _ => ⟨rfl, rfl⟩) 1 counted,
    tables_success _ _ _ _ (fun o => decide (o.2 = 1)) (fun _ s => pay_shows s) 1 counted,
    tables_not_recur _ _ _ _ (fun _ => 0) counted,
    fun h => tables_unreachable _ _ _ _ (fun _ => 0) counted (bigClass_meets.mp h).1⟩

/-- Case 8. The cases reading: every condition met, big; it differs from case 7 only in when the
extra clue appears. The record: (a) fails; (b) holds, since the clue comes only once the goal is
met; success shows; the attempts do not recur; not met. -/
theorem c8 (counted : List (Answers 1000000)) :
    ¬ goalsReachable.holds (counting case8 counted) ∧
      goalsConcealed.holds (counting case8 counted) ∧
      successShows.holds (counting case8 counted) ∧
      ¬ attemptsRecur.holds (counting case8 counted) ∧
      ¬ bigClass.Meets (counting case8 counted) :=
  ⟨tables_unreachable _ _ _ _ (fun _ => 0) counted,
    tables_concealed _ _ _ _ sight pay
      (fun k s h => ⟨by
        show ((if s.2.2 then Fin.ofNat 200 (s.1.val + 100 * ((k s.1).val % 2))
          else Fin.ofNat 200 s.1.val, decide (s.2.1 = 0)) : Sight) = sight s
        rw [h]
        rfl, rfl⟩) 1 counted,
    tables_success _ _ _ _ (fun o => decide (o.2 = 1)) (fun _ s => pay_shows s) 1 counted,
    tables_not_recur _ _ _ _ (fun _ => 0) counted,
    fun h => tables_unreachable _ _ _ _ (fun _ => 0) counted (bigClass_meets.mp h).1⟩

/-- Case 10. The cases reading: every condition met, big; success shows as the reward -7. The
record: (a) fails; (b) holds; success shows, read as the reward -7; the attempts do not recur; not
met. -/
theorem c10 (counted : List (Answers 1000000)) :
    ¬ goalsReachable.holds (counting case10 counted) ∧
      goalsConcealed.holds (counting case10 counted) ∧
      successShows.holds (counting case10 counted) ∧
      ¬ attemptsRecur.holds (counting case10 counted) ∧
      ¬ bigClass.Meets (counting case10 counted) :=
  ⟨tables_unreachable _ _ _ _ (fun _ => 0) counted,
    tables_concealed _ _ _ _ sight (fun _ => 0)
      (fun _ s h => ⟨rfl, by
        show (if s.2.2 then (-7 : Rat) else 0) = 0
        rw [h]
        rfl⟩) 1 counted,
    tables_success _ _ _ _ (fun o => decide (o.2 = -7))
      (fun _ s => by
        obtain ⟨c, t, b⟩ := s
        cases b
        · show decide ((0 : Rat) = -7) = false
          decide
        · show decide ((-7 : Rat) = -7) = true
          decide) 1 counted,
    tables_not_recur _ _ _ _ (fun _ => 0) counted,
    fun h => tables_unreachable _ _ _ _ (fun _ => 0) counted (bigClass_meets.mp h).1⟩

/-- The rule the cases reading names for case 4: the button 0 on `begin`, and on `inside` the
button 0 after the reward 1 and the button 1 after any other. It reads only what it is given at the
step, so its agent keeps nothing of its experience. -/
def quick : Agent Sight (Fin 2) :=
  ruleAgent fun o => if o.1.2 then 0 else if o.2 = 1 then 0 else 1

/-- In case 4 the agent of that rule is, after two steps of its run in any member, at a state that
meets the member's goal. -/
theorem quick_solves (counted : List (Answers 2)) (k : Answers 2) :
    (counting case4 counted).solves quick k 2 = true := by
  have hrun : (counting case4 counted).stateAt quick k 2 =
      (0, 2, (if (if ((0 : Fin 2) == k 0) then (1 : Rat) else 0) = 1 then (0 : Fin 2) else 1)
        == k 0) := rfl
  refine (solves_iff (counting case4 counted) quick k 2).mpr ⟨0, Nat.lt_succ_self 0, ?_⟩
  show ((counting case4 counted).stateAt quick k 2).2.2 = true
  rw [hrun]
  show ((if (if ((0 : Fin 2) == k 0) then (1 : Rat) else 0) = 1 then (0 : Fin 2) else 1)
    == k 0) = true
  have hk : k 0 = 0 ∨ k 0 = 1 := by
    match k 0 with
    | ⟨0, _⟩ => exact Or.inl rfl
    | ⟨1, _⟩ => exact Or.inr rfl
    | ⟨n + 2, h⟩ => exact absurd h (by omega)
  rcases hk with h | h <;> rw [h] <;> decide

/-- Case 4. The cases reading: (a), (b) and (d) met, (c) not met, since a memoryless rule solves
every member on its second action, both parts of sentence 6 met, not big. The record: (a) fails;
(b) holds; (c) fails, for the same reason and whichever members are counted; success shows; the
attempts do not recur; not met. -/
theorem c4 (counted : List (Answers 2)) :
    ¬ goalsReachable.holds (counting case4 counted) ∧
      goalsConcealed.holds (counting case4 counted) ∧
      ¬ frozenShareSmall.holds (counting case4 counted) ∧
      successShows.holds (counting case4 counted) ∧
      ¬ attemptsRecur.holds (counting case4 counted) ∧
      ¬ bigClass.Meets (counting case4 counted) :=
  ⟨tables_unreachable _ _ _ _ (fun _ => 0) counted,
    tables_concealed _ _ _ _ sight pay (fun _ _ _ => ⟨rfl, rfl⟩) 1 counted,
    fun ⟨hn, _, hk, h⟩ =>
      absurd (h quick (ruleAgent_keepsNothing _) 2 counted hn fun i _ => quick_solves counted i)
        (Nat.not_le_of_lt hk),
    tables_success _ _ _ _ (fun o => decide (o.2 = 1)) (fun _ s => pay_shows s) 1 counted,
    tables_not_recur _ _ _ _ (fun _ => 0) counted,
    fun h => tables_unreachable _ _ _ _ (fun _ => 0) counted (bigClass_meets.mp h).1⟩

/-- Case 6. The cases reading: (a), (c) and (d) met, (b) not met, since the reward tells the parity
of the answer before any success, both parts of sentence 6 met, not big. The record: (a) fails; (b)
fails, for the same reason; success shows; the attempts do not recur; not met. -/
theorem c6 (counted : List (Answers 1000000)) :
    ¬ goalsReachable.holds (counting case6 counted) ∧
      ¬ goalsConcealed.holds (counting case6 counted) ∧
      successShows.holds (counting case6 counted) ∧
      ¬ attemptsRecur.holds (counting case6 counted) ∧
      ¬ bigClass.Meets (counting case6 counted) :=
  ⟨tables_unreachable _ _ _ _ (fun _ => 0) counted,
    fun ⟨_, h⟩ => by
      have e0 := h (searcher 1000000) (fun _ => 0) 0 (fun u hu => by cases Nat.le_zero.mp hu; rfl)
      have e1 := h (searcher 1000000) (fun _ => 1) 0 (fun u hu => by cases Nat.le_zero.mp hu; rfl)
      have e : (-1 : Rat) = -2 := congrArg Prod.snd (e0.trans e1.symm)
      exact absurd e (by decide),
    tables_success _ _ _ _ (fun o => decide (o.2 = 1))
      (fun k s => by
        obtain ⟨c, t, b⟩ := s
        cases b
        · show decide ((if (k c).val % 2 = 0 then (-1 : Rat) else -2) = 1) = false
          split <;> decide
        · show decide ((1 : Rat) = 1) = true
          decide) 1 counted,
    tables_not_recur _ _ _ _ (fun _ => 0) counted,
    fun h => tables_unreachable _ _ _ _ (fun _ => 0) counted (bigClass_meets.mp h).1⟩

/-- Case 7. The cases reading: (a), (c) and (d) met, (b) not met, since after a failed first action
the observation tells the parity of the answer before any success, both parts of sentence 6 met,
not big. The record: (a) fails; (b) fails, for the same reason; success shows; the attempts do not
recur; not met. -/
theorem c7 (counted : List (Answers 1000000)) :
    ¬ goalsReachable.holds (counting case7 counted) ∧
      ¬ goalsConcealed.holds (counting case7 counted) ∧
      successShows.holds (counting case7 counted) ∧
      ¬ attemptsRecur.holds (counting case7 counted) ∧
      ¬ bigClass.Meets (counting case7 counted) :=
  ⟨tables_unreachable _ _ _ _ (fun _ => 0) counted,
    fun ⟨_, h⟩ => by
      have e0 := h (searcher 1000000) (fun _ => 2) 1 (fun u hu => by
        have hu' : u = 0 ∨ u = 1 := by omega
        rcases hu' with rfl | rfl <;> rfl)
      have e1 := h (searcher 1000000) (fun _ => 1) 1 (fun u hu => by
        have hu' : u = 0 ∨ u = 1 := by omega
        rcases hu' with rfl | rfl <;> rfl)
      have e : (fun o : Sight × Rat => o.1.1.val)
            (given (case7.member fun _ => 2) (searcher 1000000) 1) =
          (fun o : Sight × Rat => o.1.1.val)
            (given (case7.member fun _ => 1) (searcher 1000000) 1) :=
        congrArg (fun o : Sight × Rat => o.1.1.val) (e0.trans e1.symm)
      exact absurd e (by decide +kernel),
    tables_success _ _ _ _ (fun o => decide (o.2 = 1)) (fun _ s => pay_shows s) 1 counted,
    tables_not_recur _ _ _ _ (fun _ => 0) counted,
    fun h => tables_unreachable _ _ _ _ (fun _ => 0) counted (bigClass_meets.mp h).1⟩

/-- Case 9. The cases reading: (a) to (d) met, neither part of sentence 6 met, since nothing
perceived tells success from failure, not big. The record: (a) fails; (b) holds; success does not
show, for the same reason; the attempts do not recur; not met. -/
theorem c9 (counted : List (Answers 1000000)) :
    ¬ goalsReachable.holds (counting case9 counted) ∧
      goalsConcealed.holds (counting case9 counted) ∧
      ¬ successShows.holds (counting case9 counted) ∧
      ¬ attemptsRecur.holds (counting case9 counted) ∧
      ¬ bigClass.Meets (counting case9 counted) :=
  ⟨tables_unreachable _ _ _ _ (fun _ => 0) counted,
    tables_concealed _ _ _ _ sight (fun _ => 0) (fun _ _ _ => ⟨rfl, rfl⟩) 1 counted,
    fun ⟨signal, h⟩ => by
      have t0 : signal ((0, false), 0) = true := h (searcher 1000000) (fun _ => 0) 1
      have t1 : signal ((0, false), 0) = false := h (searcher 1000000) (fun _ => 1) 1
      exact Bool.noConfusion (t0.symm.trans t1),
    tables_not_recur _ _ _ _ (fun _ => 0) counted,
    fun h => tables_unreachable _ _ _ _ (fun _ => 0) counted (bigClass_meets.mp h).1⟩

/-! ## Cases 11 and 12: a table world with a trap -/

/-- The table world of case 1 with a state `dead`, here `none`, and an action `poison`, here
`none`. Every action at `dead` stays there, and `poison` leads there from every other state. At
`dead` the world shows the context 0 with `begin`, pays nothing and does not meet its goal. -/
def poisoned (k : Answers 1000000) (start : Option Cell) :
    Member Sight (Option (Fin 1000000)) where
  State := Option Cell
  start := start
  observe := fun
    | none => (0, true)
    | some s => sight s
  reward := fun
    | none => 0
    | some s => pay s
  step := fun
    | none, _ => none
    | some _, none => none
    | some s, some a => some (advance (fun c a => a == k c) s a)
  goal := fun
    | none => false
    | some s => s.2.2

/-- The agent of cases 11 and 12: the agent of case 1, which never takes `poison`. -/
def careful : Agent Sight (Option (Fin 1000000)) where
  Memory := Fin 1000000
  initial := 0
  act := fun m o =>
    if o.1.2 then (some 0, 0)
    else if o.2 = 1 ∨ o.2 = -7 then (some m, m) else (some (m + 1), m + 1)

/-- Case 11: the class of case 1 with an optional trap that no member starts in. -/
def case11 : ClassWithAgent where
  Obs := Sight
  Act := Option (Fin 1000000)
  Index := Answers 1000000
  member := fun k => poisoned k (some (0, 0, false))
  length := 1
  agent := careful

/-- Case 12: the class of case 11 whose members start in the trap. -/
def case12 : ClassWithAgent where
  Obs := Sight
  Act := Option (Fin 1000000)
  Index := Answers 1000000
  member := fun k => poisoned k none
  length := 1
  agent := careful

/-- In a table world with a trap, the reward is 1 exactly where the goal is met. -/
theorem poisoned_shows (k : Answers 1000000) (start : Option Cell) (s : Option Cell) :
    decide ((poisoned k start).reward s = 1) = (poisoned k start).goal s := by
  cases s with
  | none =>
    show decide ((0 : Rat) = 1) = false
    decide
  | some s => exact pay_shows s

/-- A member that starts in the trap stays there, whatever the agent does. -/
theorem poisoned_dead (k : Answers 1000000) (A : Agent Sight (Option (Fin 1000000))) :
    ∀ t, ((poisoned k none).run A t).1 = none
  | 0 => rfl
  | t + 1 => by
    show (poisoned k none).step ((poisoned k none).run A t).1 _ = none
    rw [poisoned_dead k A t]
    rfl

/-- A member that starts outside the trap is, after an action other than `poison`, no longer in its
start state: its time is 1. -/
theorem poisoned_moves (k : Answers 1000000) (a : Fin 1000000) :
    (poisoned k (some (0, 0, false))).step (some (0, 0, false)) (some a) ≠ some (0, 0, false) := by
  intro e
  have e' : (0 + 1 : Fin 1000000000) = 0 := congrArg (fun c : Cell => c.2.1) (Option.some.inj e)
  exact absurd e' (by decide)

/-- Case 11. The cases reading: every condition met, big; the trap is one the words permit. The
record: (a) fails; success shows; the attempts do not recur; not met. Conditions (b) and (c) are
not decided here. -/
theorem c11 (counted : List (Answers 1000000)) :
    ¬ goalsReachable.holds (counting case11 counted) ∧
      successShows.holds (counting case11 counted) ∧
      ¬ attemptsRecur.holds (counting case11 counted) ∧
      ¬ bigClass.Meets (counting case11 counted) :=
  ⟨unreachable_of_short _ (fun _ => 0) (Nat.le_refl 1) rfl,
    ⟨fun o => decide (o.2 = 1), fun (A : Agent Sight (Option (Fin 1000000))) k t =>
      poisoned_shows k _ ((poisoned k (some (0, 0, false))).run A t).1⟩,
    fun h => poisoned_moves (fun _ => 0) 0 (h careful (fun _ => 0) 1),
    fun h => unreachable_of_short _ (fun _ => 0) (Nat.le_refl 1) rfl (bigClass_meets.mp h).1⟩

/-- Case 12. The cases reading: (a) not met, (b) and (c) met, (d) not met, the success signal met,
temporal coherence not met, not big. The record: (a) fails, since the members start in the trap;
success shows; the attempts recur, since the world never leaves the state it starts in; not met.
Conditions (b) and (c) are not decided here. -/
theorem c12 (counted : List (Answers 1000000)) :
    ¬ goalsReachable.holds (counting case12 counted) ∧
      successShows.holds (counting case12 counted) ∧
      attemptsRecur.holds (counting case12 counted) ∧
      ¬ bigClass.Meets (counting case12 counted) :=
  ⟨unreachable_of_short _ (fun _ => 0) (Nat.le_refl 1) rfl,
    ⟨fun o => decide (o.2 = 1), fun (A : Agent Sight (Option (Fin 1000000))) k t =>
      poisoned_shows k _ ((poisoned k none).run A t).1⟩,
    fun (A : Agent Sight (Option (Fin 1000000))) k n => poisoned_dead k A (1 * n),
    fun h => unreachable_of_short _ (fun _ => 0) (Nat.le_refl 1) rfl (bigClass_meets.mp h).1⟩

/-! ## Cases 14 and 15: worlds that never return to an earlier context -/

/-- The world of cases 14 and 15 with the answers `k`: its states are a time and whether the last
action was the answer; it shows `begin`, here `true`, when the time is divisible by 1,000,000,000;
it pays 1 where the last action was the answer; and the answer at a time is that of `block` of the
time. -/
def stream (block : Nat → Nat) (k : Nat → Fin 1000000) : Member Bool (Fin 1000000) where
  State := Nat × Bool
  start := (0, false)
  observe := fun s => decide (s.1 % 1000000000 = 0)
  reward := fun s => if s.2 then 1 else 0
  step := fun s a => (s.1 + 1, a == k (block s.1))
  goal := fun s => s.2

/-- The agent of cases 14 and 15: the agent of case 1, for a world that shows only the flag. -/
def follower : Agent Bool (Fin 1000000) where
  Memory := Fin 1000000
  initial := 0
  act := fun m o => if o.1 then (0, 0) else if o.2 = 1 ∨ o.2 = -7 then (m, m) else (m + 1, m + 1)

/-- Case 14: infinitely many answers, each lasting 1,000,000,000 steps. -/
def case14 : ClassWithAgent where
  Obs := Bool
  Act := Fin 1000000
  Index := Nat → Fin 1000000
  member := stream (· / 1000000000)
  length := 1
  agent := follower

/-- Case 15: a fresh answer at every step. -/
def case15 : ClassWithAgent where
  Obs := Bool
  Act := Fin 1000000
  Index := Nat → Fin 1000000
  member := stream id
  length := 1
  agent := follower

/-- In a world of cases 14 and 15, the reward is 1 exactly where the goal is met. -/
theorem stream_shows (block : Nat → Nat) (k : Nat → Fin 1000000) (s : Nat × Bool) :
    decide ((stream block k).reward s = 1) = (stream block k).goal s := by
  obtain ⟨t, b⟩ := s
  cases b
  · show decide ((0 : Rat) = 1) = false
    decide
  · show decide ((1 : Rat) = 1) = true
    decide

/-- Case 14. The cases reading: (a), (b) and (d) met, (c) not settled, since the words give no
measure of a share of an infinite class, both parts of sentence 6 met, overall not settled. The
record: (a) fails; success shows; the attempts do not recur; not met. Conditions (b) and (c) are
not decided here. -/
theorem c14 (counted : List (Nat → Fin 1000000)) :
    ¬ goalsReachable.holds (counting case14 counted) ∧
      successShows.holds (counting case14 counted) ∧
      ¬ attemptsRecur.holds (counting case14 counted) ∧
      ¬ bigClass.Meets (counting case14 counted) :=
  ⟨unreachable_of_short _ (fun _ => 0) (Nat.le_refl 1) rfl,
    ⟨fun o => decide (o.2 = 1), fun (A : Agent Bool (Fin 1000000)) k t =>
      stream_shows (· / 1000000000) k ((stream (· / 1000000000) k).run A t).1⟩,
    fun h => by
      have e : (0 + 1 : Nat) = 0 := congrArg Prod.fst (h follower (fun _ => 0) 1)
      exact absurd e (by decide),
    fun h => unreachable_of_short _ (fun _ => 0) (Nat.le_refl 1) rfl (bigClass_meets.mp h).1⟩

/-- Case 15. The cases reading: (a), (b) and (d) met, (c) not settled, the success signal met,
temporal coherence not met, since a found answer is of no use at the next step, not big. The
record: (a) fails; success shows; the attempts do not recur; not met. Conditions (b) and (c) are
not decided here. -/
theorem c15 (counted : List (Nat → Fin 1000000)) :
    ¬ goalsReachable.holds (counting case15 counted) ∧
      successShows.holds (counting case15 counted) ∧
      ¬ attemptsRecur.holds (counting case15 counted) ∧
      ¬ bigClass.Meets (counting case15 counted) :=
  ⟨unreachable_of_short _ (fun _ => 0) (Nat.le_refl 1) rfl,
    ⟨fun o => decide (o.2 = 1), fun (A : Agent Bool (Fin 1000000)) k t =>
      stream_shows id k ((stream id k).run A t).1⟩,
    fun h => by
      have e : (0 + 1 : Nat) = 0 := congrArg Prod.fst (h follower (fun _ => 0) 1)
      exact absurd e (by decide),
    fun h => unreachable_of_short _ (fun _ => 0) (Nat.le_refl 1) rfl (bigClass_meets.mp h).1⟩

/-! ## Cases 16 and 17: a goal two steps from the start -/

/-- The states of a member of cases 16 and 17, which are also what it shows. -/
inductive Lamp where
  /-- Where the member starts. -/
  | ready
  /-- Where every action leads from every other state. -/
  | armed
  /-- The goal: the action taken at `armed` was the member's. -/
  | hit
  /-- The action taken at `armed` was not the member's. -/
  | miss
  deriving DecidableEq

/-- The member of cases 16 and 17 whose button is `k`: from `armed` the button `k` leads to `hit`
and every other to `miss`; from every other state every action leads to `armed`. It shows its
state and pays 1 at `hit`. -/
def lamp (k : Fin 1000000) : Member Lamp (Fin 1000000) where
  State := Lamp
  start := .ready
  observe := id
  reward := fun
    | .hit => 1
    | _ => 0
  step := fun
    | .armed, a => bif a == k then .hit else .miss
    | _, _ => .armed
  goal := fun
    | .hit => true
    | _ => false

/-- The agent of cases 16 and 17. Shown `ready`, it outputs the button 0 and keeps 0; shown `miss`,
it outputs its memory plus one and keeps that; shown `armed` or `hit`, it outputs its memory and
keeps it. It ignores the reward. -/
def lampAgent : Agent Lamp (Fin 1000000) where
  Memory := Fin 1000000
  initial := 0
  act := fun m o =>
    match o.1 with
    | .ready => (0, 0)
    | .miss => (m + 1, m + 1)
    | _ => (m, m)

/-- Case 16: a goal two steps from the start, with attempts of one step. -/
def case16 : ClassWithAgent where
  Obs := Lamp
  Act := Fin 1000000
  Index := Fin 1000000
  member := lamp
  length := 1
  agent := lampAgent

/-- Case 17: the class of case 16 with attempts of two steps. -/
def case17 : ClassWithAgent where
  Obs := Lamp
  Act := Fin 1000000
  Index := Fin 1000000
  member := lamp
  length := 2
  agent := lampAgent

/-- A member of cases 16 and 17 shows `hit` exactly where its goal is met. -/
theorem lamp_shows (k : Fin 1000000) (s : Lamp) :
    decide ((lamp k).observe s = Lamp.hit) = (lamp k).goal s := by
  cases s <;> rfl

/-- Case 16. The cases reading: (a) not settled, since the words do not say whether the goal must
be reachable within an attempt, (b) and (c) met, (d) not met, both parts of sentence 6 met, not
big. The record: (a) fails; success shows; the attempts do not recur; not met. Conditions (b) and
(c) are not decided here. -/
theorem c16 (counted : List (Fin 1000000)) :
    ¬ goalsReachable.holds (counting case16 counted) ∧
      successShows.holds (counting case16 counted) ∧
      ¬ attemptsRecur.holds (counting case16 counted) ∧
      ¬ bigClass.Meets (counting case16 counted) :=
  ⟨unreachable_of_short _ (0 : Fin 1000000) (Nat.le_refl 1) rfl,
    ⟨fun (o : Lamp × Rat) => decide (o.1 = Lamp.hit), fun (A : Agent Lamp (Fin 1000000)) k t =>
      lamp_shows k ((lamp k).run A t).1⟩,
    fun h => by
      have e : Lamp.armed = Lamp.ready := h lampAgent (0 : Fin 1000000) 1
      exact absurd e (by decide),
    fun h => unreachable_of_short _ (0 : Fin 1000000) (Nat.le_refl 1) rfl (bigClass_meets.mp h).1⟩

/-- In case 17 the record's condition (a) fails: an attempt of two steps leaves room for one action,
and the goal is two actions from the start. -/
theorem c17_unreachable (counted : List (Fin 1000000)) :
    ¬ goalsReachable.holds (counting case17 counted) := by
  intro h
  obtain ⟨acts, hl, hg⟩ := h lampAgent (0 : Fin 1000000) 0
  have hl' : acts.length < 2 := hl
  match acts, hl', hg with
  | [], _, hg =>
    have hf : false = true := hg
    exact Bool.noConfusion hf
  | [_], _, hg =>
    have hf : false = true := hg
    exact Bool.noConfusion hf
  | _ :: _ :: rest, hl', _ =>
    have hl'' : rest.length + 1 + 1 < 2 := hl'
    omega

/-- Case 17. The cases reading: (a) to (c) met, (d) not met, both parts of sentence 6 met, not big;
an attempt of two steps reaches a goal two actions away. The record: (a) fails, since it counts as
an attempt's times its start and the states after all but its last step; success shows; the
attempts do not recur; not met. Conditions (b) and (c) are not decided here. -/
theorem c17 (counted : List (Fin 1000000)) :
    ¬ goalsReachable.holds (counting case17 counted) ∧
      successShows.holds (counting case17 counted) ∧
      ¬ attemptsRecur.holds (counting case17 counted) ∧
      ¬ bigClass.Meets (counting case17 counted) :=
  ⟨c17_unreachable counted,
    ⟨fun (o : Lamp × Rat) => decide (o.1 = Lamp.hit), fun (A : Agent Lamp (Fin 1000000)) k t =>
      lamp_shows k ((lamp k).run A t).1⟩,
    fun h => by
      have e : Lamp.hit = Lamp.ready := h lampAgent (0 : Fin 1000000) 1
      exact absurd e (by decide),
    fun h => c17_unreachable counted (bigClass_meets.mp h).1⟩

/-! ## Cases 18 to 20: attempts of no step -/

/-- The one member of cases 18 and 19: a switch that is `on`, here `true`, or `off`, shows which,
pays 1 when `on`, meets its goal exactly when `on`, and is turned `on` by its one action. -/
def switch (start : Bool) : Member Bool Unit where
  State := Bool
  start := start
  observe := id
  reward := fun s => if s then 1 else 0
  step := fun _ _ => true
  goal := id

/-- Case 18: one member that starts at its goal, attempts of no step, and an agent of one
memory. -/
def case18 : ClassWithAgent where
  Obs := Bool
  Act := Unit
  Index := Unit
  member := fun _ => switch true
  length := 0
  agent := always ()

/-- Case 19: the class of case 18 whose member starts outside its goal. -/
def case19 : ClassWithAgent where
  Obs := Bool
  Act := Unit
  Index := Unit
  member := fun _ => switch false
  length := 0
  agent := always ()

/-- Case 20: a class with no member. -/
def case20 : ClassWithAgent where
  Obs := Bool
  Act := Unit
  Index := Empty
  member := fun i => nomatch i
  length := 0
  agent := always ()

/-- Where an attempt lasts no step and the class counts one member, the record's condition (c)
holds: no agent solves any member, so the bound is 0. -/
theorem share_of_zero (w : Trial) (hlen : w.length = 0) (i : w.Index) (hc : w.counted = [i]) :
    frozenShareSmall.holds w := by
  refine ⟨by rw [hc]; exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, 0,
    by rw [hc]; exact Nat.lt_succ_self 0, fun B _ n l _ hs => ?_⟩
  match l, hs with
  | [], _ => exact Nat.le_refl 0
  | j :: _, hs =>
    have ht := hs j (List.mem_cons_self ..)
    rw [solves_of_zero w hlen B j n] at ht
    exact Bool.noConfusion ht

/-- Case 18. The cases reading: (a) and (b) met, (c) not met, since every agent succeeds at once on
the whole class, (d) not met, the success signal met, temporal coherence not met, not big. The
record, which gives an attempt of no step no time at which a goal could be met: (a) fails; (b)
holds; (c) holds when the one member is counted, since nobody solves it; success shows; the
attempts recur; not met. -/
theorem c18 :
    ¬ goalsReachable.holds (counting case18 [()]) ∧
      goalsConcealed.holds (counting case18 [()]) ∧
      frozenShareSmall.holds (counting case18 [()]) ∧
      successShows.holds (counting case18 [()]) ∧
      attemptsRecur.holds (counting case18 [()]) ∧
      ¬ bigClass.Meets (counting case18 [()]) :=
  ⟨unreachable_of_zero _ () rfl,
    ⟨switch true, fun _ _ _ _ => rfl⟩,
    share_of_zero _ rfl () rfl,
    ⟨fun o => o.1, fun _ _ _ => rfl⟩,
    fun (A : Agent Bool Unit) _ n => by
      show ((switch true).run A (0 * n)).1 = true
      rw [Nat.zero_mul]
      rfl,
    fun h => unreachable_of_zero _ () rfl (bigClass_meets.mp h).1⟩

/-- Case 19. The cases reading: (a) not settled, (b) and (c) met, (d) not met, the success signal
met, temporal coherence not met, not big. The record: (a) fails; (b) holds; (c) holds when the one
member is counted; success shows; the attempts recur; not met. -/
theorem c19 :
    ¬ goalsReachable.holds (counting case19 [()]) ∧
      goalsConcealed.holds (counting case19 [()]) ∧
      frozenShareSmall.holds (counting case19 [()]) ∧
      successShows.holds (counting case19 [()]) ∧
      attemptsRecur.holds (counting case19 [()]) ∧
      ¬ bigClass.Meets (counting case19 [()]) :=
  ⟨unreachable_of_zero _ () rfl,
    ⟨switch false, fun _ _ _ _ => rfl⟩,
    share_of_zero _ rfl () rfl,
    ⟨fun o => o.1, fun _ _ _ => rfl⟩,
    fun (A : Agent Bool Unit) _ n => by
      show ((switch false).run A (0 * n)).1 = false
      rw [Nat.zero_mul]
      rfl,
    fun h => unreachable_of_zero _ () rfl (bigClass_meets.mp h).1⟩

/-- In case 20 the record's condition (c) fails: a class with no member counts none. -/
theorem c20_share (counted : List Empty) :
    ¬ frozenShareSmall.holds (counting case20 counted) := fun ⟨_, k, hk, _⟩ =>
  match counted, hk with
  | [], hk => Nat.not_lt_zero k hk
  | i :: _, _ => nomatch i

/-- Case 20. The cases reading: (a) and (b) met, (c) not settled, since a share of an empty class
has no meaning the words give, (d) not met, the success signal met, temporal coherence not met, not
big. The record: (a) and (b) hold, of no member; (c) fails, since a class with no member counts
none; success shows and the attempts recur, of no member; not met. -/
theorem c20 (counted : List Empty) :
    goalsReachable.holds (counting case20 counted) ∧
      goalsConcealed.holds (counting case20 counted) ∧
      ¬ frozenShareSmall.holds (counting case20 counted) ∧
      successShows.holds (counting case20 counted) ∧
      attemptsRecur.holds (counting case20 counted) ∧
      ¬ bigClass.Meets (counting case20 counted) :=
  ⟨(fun _ (i : Empty) _ => nomatch i),
    ⟨switch true, (fun _ (i : Empty) _ _ => nomatch i)⟩,
    c20_share counted,
    ⟨fun _ => true, (fun _ (i : Empty) _ => nomatch i)⟩,
    (fun _ (i : Empty) _ => nomatch i),
    fun h => c20_share counted (bigClass_meets.mp h).2.2.1⟩

end AcornVerif.Intent.BigClass.Cases
