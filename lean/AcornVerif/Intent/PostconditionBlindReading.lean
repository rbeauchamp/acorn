/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.PostconditionSubject

/-!
# The blind record reading of the postcondition

This module holds the second, blind reading of the postcondition's six sentences and of the owner's
two decisions of 2026-11-17 that OpenAI's gpt-6-astra made as a record over the subject's type, in
one session on 2026-11-18, after the record `AcornVerif.Intent.Postcondition.postcondition` and its
adequacy proofs were on Acorn's main branch at commit 453cee1. It is no deliverable and no part of
the owner's intent: it is a second model's reading of the owner's words. Its comparison with the
record is in `AcornVerif.Intent.PostconditionBlindCompare`, and how each difference was settled is
in the record's confirmation file, `lean/AcornVerif/Intent/Postcondition.md`, which also says what
the session was given and how it was kept from the record.

The module imports the module of the subject's types, `AcornVerif.Intent.PostconditionSubject`, and
not the record's, so no definition of the record enters it.

The namespace `AcornOwnerIntent` is the blind reader's own name, kept as returned. The module
declares exactly the declarations of the Lean file in the blind reader's reply from that namespace
on, with the same names, statements, definition bodies and comments. Its text differs from that file
only in these ways:

* The reply's file began by repeating the three structures it was given, `Agent`, `Member` and
  `Trial`, without their docstrings, "so that it needs only the requested import". They are removed,
  and the module imports `AcornVerif.Intent.PostconditionSubject`, which declares `Member` and
  `Trial` and imports the module that declares `Agent`.
* The import of `LeanIntent.Record` is removed: the merge gate's boundary audit admits an import of
  lean-intent in `AcornVerif.LeanIntentBridge` alone, and the subject's module reaches lean-intent's
  record module through it.
* This copyright header and this module docstring are added.
* A docstring is added to each declaration the missing-docs linter flags: `evolve`, `run`,
  `inputAt`, `Solves`, `attemptReturn`, `sumRat`, `sumNat`, `classReward`, `classSolved`,
  `Compared`, `laterFailures`, the structure `FixedData` and its eleven fields, `fixedData`,
  `unbox`, `trialShape`, `ownerProperties` and the record `intent`.

Lean elaborated the reply's text with no other change. The reply said that its Lean had not been
compiler-checked.
-/

namespace AcornOwnerIntent

open LeanIntent
open AcornVerif.Intent.WorldInterface
open AcornVerif.Intent.Postcondition

noncomputable section

/- Execution and measurement. -/

/-- The world's state and the agent's memory after the given number of interactions of the agent
`a` in the world `w`, from the state `s` and the memory `m`. -/
def evolve {O A : Type}
    (w : AcornVerif.Intent.Postcondition.Member O A)
    (a : Agent O A) (s : w.State) (m : a.Memory) :
    Nat → w.State × a.Memory
  | 0 => (s, m)
  | n + 1 =>
      let c := evolve w a s m n
      let answer := a.act c.2 (w.observe c.1, w.reward c.1)
      (w.step c.1 answer.1, answer.2)

/-- The state of the member `i` and the memory of the agent `a` after `k` interactions of its run in
that member, from the member's start and the agent's initial memory. -/
def run (t : Trial) (a : Agent t.Obs t.Act) (i : t.Index)
    (k : Nat) : (t.member i).State × a.Memory :=
  evolve (t.member i) a (t.member i).start a.initial k

/-- What the agent `a` is given at interaction `k` of its run in the member `i`: the member's
observation and reward at the state then. -/
def inputAt (t : Trial) (a : Agent t.Obs t.Act) (i : t.Index)
    (k : Nat) : t.Obs × Rat :=
  let s := (run t a i k).1
  ((t.member i).observe s, (t.member i).reward s)

/--
An attempt consists of `length` successive observation/reward/action
interactions. Its sampled states have offsets 0, ..., length - 1.
World transitions, including restarts, remain the world's own transitions.
-/
def solvedB (t : Trial) (a : Agent t.Obs t.Act) (i : t.Index)
    (attempt : Nat) : Bool :=
  (List.range t.length).any fun offset =>
    (t.member i).goal
      (run t a i (attempt * t.length + offset)).1

/-- The agent `a` solves the member `i` on the attempt. -/
def Solves (t : Trial) (a : Agent t.Obs t.Act) (i : t.Index)
    (attempt : Nat) : Prop :=
  solvedB t a i attempt = true

/-- The class's aggregate of the rewards the agent `a` is given on the attempt of its run in the
member `i`. -/
def attemptReturn (t : Trial) (a : Agent t.Obs t.Act)
    (i : t.Index) (attempt : Nat) : Rat :=
  t.total ((List.range t.length).map fun offset =>
    (inputAt t a i (attempt * t.length + offset)).2)

/-- The sum of a list of rational numbers. -/
def sumRat : List Rat → Rat
  | [] => 0
  | x :: xs => x + sumRat xs

/-- The sum of a list of natural numbers. -/
def sumNat : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumNat xs

/-- The sum, over the counted members, of what the agent `a` earns on the attempt. -/
def classReward (t : Trial) (a : Agent t.Obs t.Act)
    (attempt : Nat) : Rat :=
  sumRat (t.counted.map fun i => attemptReturn t a i attempt)

/-- How many of the counted members the agent `a` solves on the attempt. -/
def classSolved (t : Trial) (a : Agent t.Obs t.Act)
    (attempt : Nat) : Nat :=
  sumNat (t.counted.map fun i =>
    if solvedB t a i attempt then 1 else 0)

/-- Reward accumulated through attempt `last`, inclusive. -/
def streamReward (t : Trial) (a : Agent t.Obs t.Act)
    (last : Nat) : Rat :=
  sumRat ((List.range (last + 1)).map fun n => classReward t a n)

/-- Successful member-attempts through attempt `last`, inclusive. -/
def streamSolved (t : Trial) (a : Agent t.Obs t.Act)
    (last : Nat) : Nat :=
  sumNat ((List.range (last + 1)).map fun n => classSolved t a n)

/- Vocabulary of behavioral predicates. -/

/--
Memory cannot affect this agent's action. This admits agents with unused
memory, as well as agents whose memory type is Unit.
-/
def KeepsNoExperience {O A : Type} (a : Agent O A) : Prop :=
  ∀ (m₁ m₂ : a.Memory) (input : O × Rat),
    (a.act m₁ input).1 = (a.act m₂ input).1

/-- The agents compared: the learning agent, and every agent that keeps no experience. -/
def Compared (t : Trial) (a : Agent t.Obs t.Act) : Prop :=
  a = t.agent ∨ KeepsNoExperience a

/-- This requirement is built into the execution convention above. -/
def ReceivesWorldReward (t : Trial) : Prop :=
  ∀ (a : Agent t.Obs t.Act) (i : t.Index) (k : Nat),
    (inputAt t a i k).2 =
      (t.member i).reward (run t a i k).1

/--
The equivalence is required for both individual counted attempts and
the accumulated stream prefixes used to read the advantage.
-/
def RewardAndSolvingAgree (t : Trial) : Prop :=
  ∀ (a b : Agent t.Obs t.Act),
    Compared t a → Compared t b →
    ∀ n, n < t.horizon →
      ((classReward t a n > classReward t b n) ↔
        (classSolved t a n > classSolved t b n)) ∧
      ((streamReward t a n > streamReward t b n) ↔
        (streamSolved t a n > streamSolved t b n))

/--
The same learning point works against every agent that keeps no
experience. The readings are nonvacuously before the stated horizon.

Comparing accumulated totals is equivalent to comparing their
per-attempt averages, since the compared prefixes have equal lengths.
-/
def EventuallyMoreRewardBeforeHorizon (t : Trial) : Prop :=
  ∃ learnedAt : Nat,
    learnedAt < t.horizon ∧
    ∀ n, learnedAt ≤ n → n < t.horizon →
      ∀ b : Agent t.Obs t.Act,
        KeepsNoExperience b →
        streamReward t t.agent n > streamReward t b n

/--
Every attempt in this interval starts from the state from which the
successful attempt started. The member's rules are already fixed.
-/
def SameAttemptStarts (t : Trial) (i : t.Index)
    (first last : Nat) : Prop :=
  ∀ n, first ≤ n → n ≤ last →
    (run t t.agent i (n * t.length)).1 =
      (run t t.agent i (first * t.length)).1

/-- How many of the attempts after `first`, up to `last`, the learning agent fails the member `i`
on. -/
def laterFailures (t : Trial) (i : t.Index)
    (first last : Nat) : Nat :=
  ((List.range (last - first)).filter fun offset =>
    !(solvedB t t.agent i (first + 1 + offset))).length

/--
After success, each unchanged interval before the horizon contains
at most the stated number of later failed attempts.
-/
def SolvesAgainWithAtMostStatedLapses (t : Trial) : Prop :=
  ∀ (i : t.Index) (first last : Nat),
    first ≤ last →
    last < t.horizon →
    Solves t t.agent i first →
    SameAttemptStarts t i first last →
    laterFailures t i first last ≤ t.lapses

/--
Re-presenting the same problem from state `s`, with the learner's
current memory, permits success after finitely many interactions.
There is no stated bound on that number.
-/
def CanLearnAgain (t : Trial) (i : t.Index)
    (s : (t.member i).State) (m : t.agent.Memory) : Prop :=
  ∃ k : Nat,
    (t.member i).goal
      (evolve (t.member i) t.agent s m k).1 = true

/--
The ability survives at every later attempt boundary in the stream,
including boundaries beyond the retention horizon.
-/
def KeepsAbilityToLearnAgain (t : Trial) : Prop :=
  ∀ (i : t.Index) (first later : Nat),
    first < later →
    Solves t t.agent i first →
    CanLearnAgain t i
      (run t t.agent i (first * t.length)).1
      (run t t.agent i (later * t.length)).2

/- Shape: fixed data plus the world's and agent's functions. -/

/-- The plain values of a trial. -/
structure FixedData where
  /-- What the worlds show. -/
  Obs : Type
  /-- The actions. -/
  Act : Type
  /-- The names of the members. -/
  Index : Type
  /-- The learning agent's memories. -/
  Memory : Type
  /-- Each member's states. -/
  state : Index → Type
  /-- Each member's state when a run begins. -/
  start : (i : Index) → state i
  /-- The learning agent's memory when a run begins. -/
  initial : Memory
  /-- The members the comparison counts. -/
  counted : List Index
  /-- How long an attempt lasts. -/
  length : Nat
  /-- The horizon. -/
  horizon : Nat
  /-- The lapses. -/
  lapses : Nat

/-- The plain values of the trial `t`. -/
def fixedData (t : Trial) : FixedData where
  Obs := t.Obs
  Act := t.Act
  Index := t.Index
  Memory := t.agent.Memory
  state := fun i => (t.member i).State
  start := fun i => (t.member i).start
  initial := t.agent.initial
  counted := t.counted
  length := t.length
  horizon := t.horizon
  lapses := t.lapses

/--
The subject chooses its own carrier types. Boxes give Shape.Member
a fixed input/output type without changing those carriers.
-/
abbrev Box := Σ A : Type, A

/-- The value a box holds, when it is of the type `A`. -/
def unbox (A : Type) (x : Box) : Option A := by
  classical
  exact if h : x.1 = A then some (cast h x.2) else none

/--
A mismatched box uses a fixed default input. Consequently a constant
underlying function remains constant in this representation.
An empty underlying domain gives the constant result `none`.
-/
def expose {A B : Type} (f : A → B) (x : Box) : Option Box := by
  classical
  exact if h : Nonempty A then
    some ⟨B, f ((unbox A x).getD (Classical.choice h))⟩
  else
    none

/-- The shape of a trial: its plain values, and each function of its worlds and of its agent. -/
def trialShape : Shape Trial :=
  .bundle fixedData
    { name := "How an attempt's rewards are aggregated"
      In := Box
      Out := Option Box
      get := fun t => expose t.total }
    [
      { name := "What each world shows"
        In := Box
        Out := Option Box
        get := fun t =>
          expose (fun p : (Σ i : t.Index, (t.member i).State) =>
            (t.member p.1).observe p.2) },
      { name := "Each world's whole reward function"
        In := Box
        Out := Option Box
        get := fun t =>
          expose (fun p : (Σ i : t.Index, (t.member i).State) =>
            (t.member p.1).reward p.2) },
      { name := "Each world's goal"
        In := Box
        Out := Option Box
        get := fun t =>
          expose (fun p : (Σ i : t.Index, (t.member i).State) =>
            (t.member p.1).goal p.2) },
      { name := "Each world's dynamics, including restarts"
        In := Box
        Out := Option Box
        get := fun t =>
          expose
            (fun p :
                (Σ i : t.Index, (t.member i).State × t.Act) =>
              (⟨p.1, (t.member p.1).step p.2.1 p.2.2⟩ :
                Σ i : t.Index, (t.member i).State)) },
      { name := "The learner's action and next memory"
        In := Box
        Out := Option Box
        get := fun t =>
          expose (fun p : t.agent.Memory × (t.Obs × Rat) =>
            t.agent.act p.1 p.2) }
    ]

/-- The five properties, in order. -/
def ownerProperties : List (Clause Trial) :=
  [
    { name := "The agent receives the world's scalar reward"
      holds := ReceivesWorldReward },
    { name := "More reward means more members solved, in both directions"
      holds := RewardAndSolvingAgree },
    { name := "Experience eventually gives more reward before the horizon"
      holds := EventuallyMoreRewardBeforeHorizon },
    { name := "Solved problems stay solved with at most the stated lapses"
      holds := SolvesAgainWithAtMostStatedLapses },
    { name := "The ability to learn a solved problem again is kept"
      holds := KeepsAbilityToLearnAgain }
  ]

/-- The blind reader's record. -/
def intent : IntentRecord Trial where
  shape := trialShape

  -- No additional unconditional facts about the environment are assumed.
  -- The equal-start condition is explicit within the retention property.
  dom := []

  props := ownerProperties

  vocab :=
    ownerProperties.map (fun c =>
      ({ name := c.name, Arg := Trial, holds := c.holds } : Pred.{1}))
    ++
    [
      { name := "Keeps nothing of experience"
        Arg := Σ t : Trial, Agent t.Obs t.Act
        holds := fun x => KeepsNoExperience x.2 },
      { name := "Is one of the agents compared"
        Arg := Σ t : Trial, Agent t.Obs t.Act
        holds := fun x => Compared x.1 x.2 },
      { name := "Solves this member on this attempt"
        Arg := Σ t : Trial,
          Agent t.Obs t.Act × (t.Index × Nat)
        holds := fun x =>
          Solves x.1 x.2.1 x.2.2.1 x.2.2.2 },
      { name := "The member's attempts start from the same state"
        Arg := Σ t : Trial, t.Index × (Nat × Nat)
        holds := fun x =>
          SameAttemptStarts x.1 x.2.1 x.2.2.1 x.2.2.2 },
      { name := "Can learn this problem again from this memory"
        Arg := Σ t : Trial,
          Σ i : t.Index, (t.member i).State × t.agent.Memory
        holds := fun x =>
          CanLearnAgain x.1 x.2.1 x.2.2.1 x.2.2.2 }
    ]

end

end AcornOwnerIntent
