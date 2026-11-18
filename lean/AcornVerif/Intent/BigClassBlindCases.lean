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

end AcornVerif.Intent.BigClass.Cases
