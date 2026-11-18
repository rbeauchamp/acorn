/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.BigClassBlindReading
import AcornVerif.Intent.BigClassConsequences

/-!
# The record of contract 2 compared with its blind record reading

The blind record, `AcornVerif.Intent.BigClassBlind.AcornOwnerIntent.ownerIntent`, is one record for
each meaning of its qualitative vocabulary, so no theorem here chooses a meaning: a comparison that
did would agree by construction. This module compares what the blind record states in closed form
with the record `AcornVerif.Intent.BigClass.bigClass`, through `shown`, what the blind sessions
were given of a trial. Every class with an agent is what they were given of some trial
(`shown_onto`). How each difference was settled is in the record's confirmation file,
`lean/AcornVerif/Intent/BigClass.md`.

* **Condition (a).** The blind record asks that every member's goal be reachable from the member's
  start by some list of actions, of any length; the record asks that it be reachable within an
  attempt from where each attempt starts. The record's gives the blind record's
  (`reachable_of_mine`). Where attempts have a step and recur, the blind record's gives the
  record's (`reachable_of_theirs`): the part of the list after the last restart it passes reaches
  the goal. Where attempts do not recur they can differ: `far`, whose goal lies two steps from its
  start with attempts of two steps, meets the blind record's and not the record's (`far_theirs`,
  `far_not_mine`).
* **The agents of condition (c).** The blind record's agents that keep nothing are the memoryless
  rules, which read what they are given at the step and nothing else. Each is an agent that keeps
  nothing of its experience in the record's sense (`ruleAgent_keepsNothing`), with the same states
  (`memorylessState_eq`). The record's agents are more: one that counts its steps keeps nothing of
  its experience and is no memoryless rule. In `clocked` no memoryless rule solves both members
  (`clocked_rule`) and a player that counts its steps solves both (`clocked_player`), so the
  record's condition (c) fails of it (`clocked_not_mine`).
* **When a member is solved.** The blind record counts the state after an attempt's last step, and
  the record does not. Where attempts have a step and recur the two agree on a memoryless rule's
  first attempt (`memorylessSolves_iff`): that state is the member's start, which both count.

What the blind record takes as a parameter is not compared here: what a small share is and of
what, the agent's resources (sentence 1 and condition (d)), what tells the agent of its goal
(condition (b)), both parts of sentence 6, the comparison of sentence 3 and the aim of sentence 7.
-/

namespace AcornVerif.Intent.BigClass.Compare

open LeanIntent WorldInterface Postcondition
open BigClassBlind (ClassWithAgent)
open BigClassBlind.AcornOwnerIntent (everyGoalReachable memorylessState memorylessSolves)

/-- What the blind sessions were given of a trial: its observations, actions, members, attempt
length and agent, without the members it counts, its aggregation, its horizon and its lapses. -/
def shown (w : Trial) : ClassWithAgent where
  Obs := w.Obs
  Act := w.Act
  Index := w.Index
  member := w.member
  length := w.length
  agent := w.agent

/-- Every class with an agent is what the blind sessions were given of a trial, whatever members
that trial counts, however it aggregates reward and whatever its horizon and lapses. -/
theorem shown_onto (c : ClassWithAgent) (counted : List c.Index) (total : List Rat → Rat)
    (horizon lapses : Nat) :
    shown { Obs := c.Obs, Act := c.Act, Index := c.Index, member := c.member, counted := counted,
            length := c.length, total := total, horizon := horizon, lapses := lapses,
            agent := c.agent } = c :=
  rfl

/-! ## Condition (a) -/

/-- The blind record follows a list of actions as the record does. -/
theorem follow_eq {Obs Act : Type} (M : Member Obs Act) :
    ∀ (acts : List Act) (s : M.State),
      BigClassBlind.AcornOwnerIntent.follow M s acts = afterActions M s acts
  | [], _ => rfl
  | a :: acts, s => follow_eq M acts (M.step s a)

/-- **The record's condition (a) gives the blind record's.** Where every member's goal can be
reached within an attempt from the state each attempt starts in, every member's goal is reachable
from the member's start. -/
theorem reachable_of_mine {w : Trial} (h : goalsReachable.holds w) :
    everyGoalReachable (shown w) := by
  intro i
  obtain ⟨acts, _, hg⟩ := h w.agent i 0
  show ∃ actions : List w.Act, (w.member i).goal
    (BigClassBlind.AcornOwnerIntent.follow (w.member i) (w.member i).start actions) = true
  exact ⟨acts, by rw [follow_eq]; exact hg⟩

/-- The agent that takes the actions of a list in order and the action `a` once the list is spent.
Its memory counts its steps, so it keeps nothing of its experience. -/
def player {Obs Act : Type} (l : List Act) (a : Act) : Agent Obs Act where
  Memory := Nat
  initial := 0
  act := fun t _ => (l.getD t a, t + 1)

theorem player_keepsNothing {Obs Act : Type} (l : List Act) (a : Act) :
    KeepsNothing (player (Obs := Obs) l a) :=
  fun _ _ _ => rfl

/-- After `t` steps of its run in any member, a player has counted `t` steps. -/
theorem player_memory {Obs Act : Type} (M : Member Obs Act) (l : List Act) (a : Act) :
    ∀ t, (M.run (player l a) t).2 = t
  | 0 => rfl
  | t + 1 => congrArg (· + 1) (player_memory M l a t)

/-- After `t` steps of a player's run in a member, the member is in the state following the list
for `t` steps leads to. -/
theorem player_state {Obs Act : Type} (M : Member Obs Act) (l : List Act) (a : Act) :
    ∀ t, (M.run (player l a) t).1 = follow M a M.start l t
  | 0 => (follow_zero M a M.start l).symm
  | t + 1 => by
    show M.step (M.run (player l a) t).1 (l.getD (M.run (player l a) t).2 a) = _
    rw [player_memory, player_state M l a t, follow_succ]

/-- Following a list for no more steps than it has actions reaches the state after that many of
its actions. -/
theorem follow_take {Obs Act : Type} (M : Member Obs Act) (a : Act) :
    ∀ (t : Nat) (l : List Act) (s : M.State), t ≤ l.length →
      follow M a s l t = afterActions M s (l.take t)
  | 0, l, s, _ => follow_zero M a s l
  | t + 1, [], _, h => absurd h (Nat.not_succ_le_zero t)
  | t + 1, x :: l, s, h => follow_take M a t l (M.step s x) (Nat.le_of_succ_le_succ h)

/-- **Where attempts have a step and recur, the blind record's condition (a) gives the record's.**
In a class whose attempts have at least one step and all start from the member's start, a goal
reachable from the start by any list of actions is reachable within an attempt from where each
attempt starts: the part of the list after the last restart it passes reaches it. -/
theorem reachable_of_theirs {w : Trial} (hL : 0 < w.length) (hrecur : attemptsRecur.holds w)
    (h : everyGoalReachable (shown w)) : goalsReachable.holds w := by
  intro A i n
  have hi : ∃ acts : List w.Act, (w.member i).goal
      (BigClassBlind.AcornOwnerIntent.follow (w.member i) (w.member i).start acts) = true := h i
  obtain ⟨acts, hg⟩ := hi
  have hg' : (w.member i).goal (afterActions (w.member i) (w.member i).start acts) = true := by
    rw [← follow_eq]
    exact hg
  have a : w.Act := (w.agent.act w.agent.initial ((w.member i).observe (w.member i).start, 0)).1
  have hq : w.length * (acts.length / w.length) ≤ acts.length := Nat.mul_div_le _ _
  have hback : afterActions (w.member i) (w.member i).start
      (acts.take (w.length * (acts.length / w.length))) = (w.member i).start := by
    rw [← follow_take (w.member i) a _ acts _ hq, ← player_state]
    exact hrecur (player acts a) i (acts.length / w.length)
  refine ⟨acts.drop (w.length * (acts.length / w.length)), ?_, ?_⟩
  · rw [List.length_drop]
    have hmod := Nat.mod_lt acts.length hL
    have hsum := Nat.div_add_mod acts.length w.length
    omega
  · rw [hrecur A i n]
    have hsplit : afterActions (w.member i) (w.member i).start acts =
        afterActions (w.member i)
          (afterActions (w.member i) (w.member i).start
            (acts.take (w.length * (acts.length / w.length))))
          (acts.drop (w.length * (acts.length / w.length))) := by
      show List.foldl _ _ acts = List.foldl _ (List.foldl _ _ _) _
      rw [← List.foldl_append, List.take_append_drop]
    rw [hsplit, hback] at hg'
    exact hg'

/-- A class whose one member's goal lies two steps from its start, with attempts of two steps. -/
def far : Trial where
  Obs := Unit
  Act := Unit
  Index := Unit
  member := fun _ =>
    { State := Nat, start := 0, observe := fun _ => (), reward := fun _ => 0,
      step := fun s _ => s + 1, goal := fun s => s == 2 }
  counted := [()]
  length := 2
  total := List.sum
  horizon := 1
  lapses := 0
  agent := always ()

/-- The blind record's condition (a) holds of `far`: two actions reach its goal. -/
theorem far_theirs : everyGoalReachable (shown far) :=
  fun _ => ⟨[(), ()], rfl⟩

/-- The record's condition (a) fails of `far`: no list of fewer than two actions reaches its goal.
So by `reachable_of_theirs` and `far_theirs` its attempts do not recur. -/
theorem far_not_mine : ¬ goalsReachable.holds far := by
  intro h
  obtain ⟨acts, hlen, hg⟩ := h (always ()) () 0
  match acts, hlen, hg with
  | [], _, hg => exact absurd hg (by decide)
  | [()], _, hg => exact absurd hg (by decide)
  | _ :: _ :: rest, hlen, _ =>
    exact absurd hlen (by show ¬ (rest.length + 1 + 1 < 2); omega)

/-! ## The agents of condition (c) -/

/-- The agent that answers by a rule of what it is given at the step, and has one memory. -/
def ruleAgent {Obs Act : Type} (answer : Obs × Rat → Act) : Agent Obs Act where
  Memory := Unit
  initial := ()
  act := fun _ o => (answer o, ())

/-- **Every memoryless rule of the blind record is an agent that keeps nothing of its experience**,
in the record's sense. -/
theorem ruleAgent_keepsNothing {Obs Act : Type} (answer : Obs × Rat → Act) :
    KeepsNothing (ruleAgent answer) :=
  fun _ _ _ => rfl

/-- The states the blind record gives a memoryless rule in a member are the states of the run of
the rule's agent in it. -/
theorem memorylessState_eq (w : Trial) (answer : w.Obs × Rat → w.Act) (i : w.Index) :
    ∀ n, memorylessState (shown w) answer i n = w.stateAt (ruleAgent answer) i n
  | 0 => rfl
  | n + 1 => by
    show (w.member i).step (memorylessState (shown w) answer i n)
        (answer ((w.member i).observe (memorylessState (shown w) answer i n),
          (w.member i).reward (memorylessState (shown w) answer i n))) =
      (w.member i).step (w.stateAt (ruleAgent answer) i n)
        (answer ((w.member i).observe (w.stateAt (ruleAgent answer) i n),
          (w.member i).reward (w.stateAt (ruleAgent answer) i n)))
    rw [memorylessState_eq w answer i n]

/-- **Where attempts have a step and recur, a memoryless rule solves a member in the blind record's
sense exactly when its agent solves the member on its first attempt in the record's.** The blind
record counts the state after an attempt's last step, and the record does not; where every attempt
starts from the member's start, that state is the start, which both count. -/
theorem memorylessSolves_iff {w : Trial} (hL : 0 < w.length) (hrecur : attemptsRecur.holds w)
    (answer : w.Obs × Rat → w.Act) (i : w.Index) :
    memorylessSolves (shown w) answer i ↔ w.solves (ruleAgent answer) i 0 = true := by
  rw [solves_iff]
  constructor
  · intro ⟨n, hn, hg⟩
    rw [memorylessState_eq] at hg
    have hn' : n ≤ w.length := hn
    rcases Nat.lt_or_eq_of_le hn' with hlt | heq
    · exact ⟨n, hlt, by rw [Nat.mul_zero, Nat.zero_add]; exact hg⟩
    · have h1 : w.stateAt (ruleAgent answer) i (w.length * 1) = (w.member i).start :=
        hrecur (ruleAgent answer) i 1
      rw [Nat.mul_one] at h1
      rw [heq, h1] at hg
      exact ⟨0, hL, hg⟩
  · intro ⟨j, hj, hg⟩
    rw [Nat.mul_zero, Nat.zero_add] at hg
    exact ⟨j, Nat.le_of_lt hj, by rw [memorylessState_eq]; exact hg⟩

/-- The states of a member of the class `clocked`. -/
inductive Stage where
  /-- Where the member starts. -/
  | first
  /-- After the first action of the member that waits for the second. -/
  | second
  /-- The goal. -/
  | won
  /-- Where a wrong action leads, for good. -/
  | lost
  deriving DecidableEq

/-- The member `b` of the class `clocked`. The member `true` is won by the action `false` at its
start and lost by the other; the member `false` moves on whatever the first action, and is won by
the action `true` there and lost by the other. Every member shows and pays the same at every
state. -/
def clockedMember (b : Bool) : Member Unit Bool where
  State := Stage
  start := .first
  observe := fun _ => ()
  reward := fun _ => 0
  step := fun
    | .first, a => bif b then (bif a then .lost else .won) else .second
    | .second, a => bif a then .won else .lost
    | s, _ => s
  goal := fun
    | .won => true
    | _ => false

/-- The class `clocked`: two members that show an agent nothing, of which one is won by its first
action and the other by its second, with attempts of three steps. -/
def clocked : Trial where
  Obs := Unit
  Act := Bool
  Index := Bool
  member := clockedMember
  counted := [true, false]
  length := 3
  total := List.sum
  horizon := 1
  lapses := 0
  agent := always false

/-- The state of the member `b` of `clocked` after `n` steps in which the action `a` is taken. -/
def constantly (a b : Bool) : Nat → Stage
  | 0 => .first
  | n + 1 => (clockedMember b).step (constantly a b n) a

/-- In `clocked` a memoryless rule takes one action throughout, since every state shows and pays
the same. -/
theorem clocked_rule_state (answer : Unit × Rat → Bool) (b : Bool) :
    ∀ n, memorylessState (shown clocked) answer b n = constantly (answer ((), 0)) b n
  | 0 => rfl
  | n + 1 => by
    show (clockedMember b).step (memorylessState (shown clocked) answer b n) (answer ((), 0)) = _
    rw [clocked_rule_state answer b n]
    rfl

/-- **In `clocked` no memoryless rule solves both members**: one action throughout wins one member
and loses the other. -/
theorem clocked_rule (answer : Unit × Rat → Bool) :
    ¬ (memorylessSolves (shown clocked) answer true ∧
      memorylessSolves (shown clocked) answer false) := by
  intro ⟨⟨n, hn, hg⟩, ⟨m, hm, hg'⟩⟩
  rw [clocked_rule_state] at hg hg'
  have hn' : n ≤ 3 := hn
  have hm' : m ≤ 3 := hm
  generalize answer ((), 0) = a at hg hg'
  cases a
  · match m, hm', hg' with
    | 0, _, h | 1, _, h | 2, _, h | 3, _, h => exact absurd h (by decide)
    | m + 4, h, _ => omega
  · match n, hn', hg with
    | 0, _, h | 1, _, h | 2, _, h | 3, _, h => exact absurd h (by decide)
    | n + 4, h, _ => omega

/-- **In `clocked` an agent that keeps nothing of its experience solves both members**: the player
of the actions `false` and then `true`, which counts its steps. So the record's condition (c),
which bounds every agent that keeps nothing of its experience, fails of `clocked`
(`clocked_not_mine`). -/
theorem clocked_player :
    KeepsNothing (player [false, true] true : Agent Unit Bool) ∧
      ∀ b ∈ ([true, false] : List Bool),
        clocked.solves (player [false, true] true : Agent Unit Bool) b 0 = true :=
  ⟨player_keepsNothing _ _, by decide⟩

theorem clocked_not_mine : ¬ frozenShareSmall.holds clocked := fun ⟨_, k, hk, h⟩ => by
  have h2 : ([true, false] : List Bool).length ≤ k :=
    h (player [false, true] true : Agent Unit Bool) (player_keepsNothing _ _) 0 [true, false]
      nodup_true_false clocked_player.2
  have hk' : k < 2 := hk
  have hl : ([true, false] : List Bool).length = 2 := rfl
  omega

end AcornVerif.Intent.BigClass.Compare
