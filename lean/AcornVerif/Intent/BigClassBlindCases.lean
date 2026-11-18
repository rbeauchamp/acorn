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

end AcornVerif.Intent.BigClass.Cases
