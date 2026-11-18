/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/

/-!
# The cases of the blind cases reading of the postcondition

This module holds the 29 cases that OpenAI's gpt-6-astra gave, in one session on 2026-11-18, as its
second, blind reading of the part of the postcondition that the owner's two decisions of 2026-11-17
read: when the advantage comes, and solving again what the agent has solved. The session was given
the owner's words and a plain description of what an input is, and no Lean type, because the
subject's type, `AcornVerif.Intent.Postcondition.Trial`, carries the record's reading of those
decisions in its fields `horizon` and `lapses`. The module imports nothing, so nothing of the record
enters it. The record's verdict on each case is in `AcornVerif.Intent.PostconditionBlindCompare`,
and how each difference was settled is in the record's confirmation file,
`lean/AcornVerif/Intent/Postcondition.md`.

An input, as the session was told, is a history: the members of a class by name; the stated attempt
and the stated number; the most members that any agent that keeps nothing of its experience could
solve on one attempt, in a class where reward counts members solved; and, for each attempt and each
member, a label of the state the member's attempt starts from and whether the learning agent solves
the member on it, listed up to some attempt and given by a rule for every later one. `History` is
that, and each case is written in it as follows.

* The reading numbers attempts from 1. The index `n` of a `History` stands for attempt `n + 1`, so
  that an index is the record's own count of attempts; `stated` keeps the reading's number.
* The members are taken in the order a case names them: Oak, then Elm, then Pine.
* A label is a number: red is 0, blue 1, gold 2 and green 3. Only whether two labels of one member
  are equal is read.
* Every case lists its first attempts and then gives one starting state and one outcome for every
  later attempt of each member. `Row` holds the listed values and the later one, and `tabled` reads
  a row at an index.
* Case 27 names no member.

Each case's docstring gives the reading's title for it and the reading's verdict. The cases are not
trials: a history says what happened and not which worlds and agent it happened in.
`AcornVerif.Intent.PostconditionBlindCompare` says what it is for a trial to show a history, and
proves that the record's verdict is the same on every trial that shows it.
-/

namespace AcornVerif.Intent.Postcondition.Cases

/-- A history, as the cases reading was told an input is: what one learning agent did, attempt by
attempt, in one class of worlds. The reading numbers attempts from 1; here the index `n` stands for
attempt `n + 1`, so that the index is the record's own count of attempts. -/
structure History where
  /-- How many members the class has; the member of index `i` is the one the case names after `i`
  others. -/
  members : Nat
  /-- The stated attempt, by its number as the reading counts attempts, from 1. -/
  stated : Nat
  /-- The stated number. -/
  number : Nat
  /-- The most members that any agent that keeps nothing of its experience could solve on one
  attempt. -/
  cap : Nat
  /-- The label of the state from which the member's attempt `n + 1` starts. -/
  start : Fin members → Nat → Nat
  /-- Whether the learning agent solves the member on attempt `n + 1`. -/
  solved : Fin members → Nat → Bool

/-- The value at each index of a table that lists its first values one by one and gives one value
for every later index. -/
def tabled {α : Type} (listed : List α) (later : α) (n : Nat) : α :=
  listed.getD n later

/-- Past the values it lists, a table gives its later value. -/
theorem tabled_later {α : Type} (listed : List α) (later : α) {n : Nat}
    (h : listed.length ≤ n) : tabled listed later n = later := by
  unfold tabled
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-- One member's row of a tabled history: the labels of the states its attempts start from, listed
one by one, with the label of every later attempt; and whether the learning agent solves it on each
attempt listed, with whether it does on every later attempt. -/
structure Row where
  /-- The labels of the starting states of the attempts listed. -/
  starts : List Nat
  /-- The label of the starting state of every later attempt. -/
  startsLater : Nat
  /-- Whether the member is solved on each attempt listed. -/
  solved : List Bool
  /-- Whether the member is solved on every later attempt. -/
  solvedLater : Bool

/-- The history whose members are the rows given, in order. -/
def History.ofRows (stated number cap : Nat) (rows : List Row) : History where
  members := rows.length
  stated := stated
  number := number
  cap := cap
  start := fun i => tabled rows[i].starts rows[i].startsLater
  solved := fun i => tabled rows[i].solved rows[i].solvedLater

/-! ## The cases -/

/-- Case 1 of the reading, "An early advantage, with successful repetition until the cutoff".
The reading's verdict: the history keeps the promise. -/
def c1 : History :=
  .ofRows 4 10 1 [
    ⟨[], 0, [false, true, true], false⟩,
    ⟨[], 1, [false, true, true], false⟩]

/-- Case 2 of the reading, "One failure inside the repetition period".
The reading's verdict: the history breaks the promise. -/
def c2 : History :=
  .ofRows 4 10 1 [
    ⟨[], 0, [false, true, true], false⟩,
    ⟨[], 1, [false, true, false], false⟩]

/-- Case 3 of the reading, "The same failure occurs at the cutoff".
The reading's verdict: the history keeps the promise. -/
def c3 : History :=
  .ofRows 3 10 1 [
    ⟨[], 0, [false, true, true], false⟩,
    ⟨[], 1, [false, true, false], false⟩]

/-- Case 4 of the reading, "The advantage itself occurs at the cutoff".
The reading's verdict: the history breaks the promise. -/
def c4 : History :=
  .ofRows 2 10 1 [
    ⟨[], 0, [false, true, true], false⟩,
    ⟨[], 1, [false, true, false], false⟩]

/-- Case 5 of the reading, "Matching the strongest agent retaining no experience".
The reading's verdict: the history breaks the promise. -/
def c5 : History :=
  .ofRows 4 10 2 [
    ⟨[], 0, [false, true, true], false⟩,
    ⟨[], 1, [false, true, true], false⟩]

/-- Case 6 of the reading, "Failure after the affected member's starting state changes".
The reading's verdict: the history keeps the promise. -/
def c6 : History :=
  .ofRows 4 10 1 [
    ⟨[], 0, [false, true, true], false⟩,
    ⟨[1, 1, 3], 3, [false, true, false], false⟩]

/-- Case 7 of the reading, "Additional successes alongside successful repetition".
The reading's verdict: the history keeps the promise. -/
def c7 : History :=
  .ofRows 5 10 1 [
    ⟨[], 0, [false, true, true, true], false⟩,
    ⟨[], 1, [false, true, true, true], false⟩,
    ⟨[], 2, [false, false, true, true], false⟩]

/-- Case 8 of the reading, "A new success compensates numerically for a temporary failure".
The reading's verdict: the history breaks the promise. -/
def c8 : History :=
  .ofRows 5 10 1 [
    ⟨[], 0, [false, true, false, true], false⟩,
    ⟨[], 1, [false, true, true, true], false⟩,
    ⟨[], 2, [false, false, true, true], false⟩]

/-- Case 9 of the reading, "Failures before a member has ever been solved".
The reading's verdict: the history keeps the promise. -/
def c9 : History :=
  .ofRows 5 10 1 [
    ⟨[], 0, [false, false, true, true], false⟩,
    ⟨[], 1, [false, false, true, true], false⟩]

/-- Case 10 of the reading, "A repetition failure before the advantage arrives".
The reading's verdict: the history breaks the promise. -/
def c10 : History :=
  .ofRows 5 10 1 [
    ⟨[], 0, [true, false, true, true], false⟩,
    ⟨[], 1, [false, false, true, true], false⟩]

/-- Case 11 of the reading, "An unsolved member can remain unsolved".
The reading's verdict: the history keeps the promise. -/
def c11 : History :=
  .ofRows 5 10 1 [
    ⟨[], 0, [false, true, true, true], false⟩,
    ⟨[], 1, [false, true, true, true], false⟩,
    ⟨[], 2, [false, false, false, false], false⟩]

/-- Case 12 of the reading, "A later first success creates a repetition obligation".
The reading's verdict: the history breaks the promise. -/
def c12 : History :=
  .ofRows 5 10 1 [
    ⟨[], 0, [false, true, true, true], false⟩,
    ⟨[], 1, [false, true, true, true], false⟩,
    ⟨[], 2, [false, false, true, false], false⟩]

/-- Case 13 of the reading, "Successful repetition followed by a changed starting state".
The reading's verdict: the history keeps the promise. -/
def c13 : History :=
  .ofRows 5 10 1 [
    ⟨[], 0, [false, true, true, true], false⟩,
    ⟨[1, 1, 1, 3], 3, [false, true, true, false], false⟩]

/-- Case 14 of the reading, "A later state change cannot excuse an earlier failure".
The reading's verdict: the history breaks the promise. -/
def c14 : History :=
  .ofRows 5 10 1 [
    ⟨[], 0, [false, true, true, true], false⟩,
    ⟨[1, 1, 1, 3], 3, [false, true, false, false], false⟩]

/-- Case 15 of the reading, "The changed starting state persists".
The reading's verdict: the history keeps the promise. -/
def c15 : History :=
  .ofRows 5 10 1 [
    ⟨[], 0, [false, true, true, true], false⟩,
    ⟨[1, 1, 3, 3], 3, [false, true, false, false], false⟩]

/-- Case 16 of the reading, "The original starting state returns".
The reading's verdict: the words do not settle this. -/
def c16 : History :=
  .ofRows 5 10 1 [
    ⟨[], 0, [false, true, true, true], false⟩,
    ⟨[1, 1, 3, 1], 1, [false, true, false, false], false⟩]

/-- Case 17 of the reading, "A stated number of zero".
The reading's verdict: the history keeps the promise. -/
def c17 : History :=
  .ofRows 4 0 1 [
    ⟨[], 0, [false, true, true], false⟩,
    ⟨[], 1, [false, true, false], false⟩]

/-- Case 18 of the reading, "A stated number of one requires the immediate repetition".
The reading's verdict: the history breaks the promise. -/
def c18 : History :=
  .ofRows 4 1 1 [
    ⟨[], 0, [false, true, true], false⟩,
    ⟨[], 1, [false, true, false], false⟩]

/-- Case 19 of the reading, "Failure after one successful repetition".
The reading's verdict: the words do not settle this. -/
def c19 : History :=
  .ofRows 6 1 1 [
    ⟨[], 0, [false, true, true, true, true], false⟩,
    ⟨[], 1, [false, true, true, false, true], false⟩]

/-- Case 20 of the reading, "The failure is within two repetitions of the first success".
The reading's verdict: the history breaks the promise. -/
def c20 : History :=
  .ofRows 6 2 1 [
    ⟨[], 0, [false, true, true, true, true], false⟩,
    ⟨[], 1, [false, true, true, false, true], false⟩]

/-- Case 21 of the reading, "More successful repetitions than the stated number".
The reading's verdict: the history keeps the promise. -/
def c21 : History :=
  .ofRows 6 1 1 [
    ⟨[], 0, [false, true, true, true, true], false⟩,
    ⟨[], 1, [false, true, true, true, true], false⟩]

/-- Case 22 of the reading, "The stated attempt is the first attempt".
The reading's verdict: the history breaks the promise. -/
def c22 : History :=
  .ofRows 1 10 1 [
    ⟨[], 0, [true, true], false⟩,
    ⟨[], 1, [true, true], false⟩]

/-- Case 23 of the reading, "Only the first attempt can supply the timely advantage".
The reading's verdict: the words do not settle this. -/
def c23 : History :=
  .ofRows 2 10 1 [
    ⟨[], 0, [true, true], false⟩,
    ⟨[], 1, [true, true], false⟩]

/-- Case 24 of the reading, "An advantage after a completed attempt".
The reading's verdict: the history keeps the promise. -/
def c24 : History :=
  .ofRows 3 10 1 [
    ⟨[], 0, [true, true], false⟩,
    ⟨[], 1, [true, true], false⟩]

/-- Case 25 of the reading, "A zero benchmark".
The reading's verdict: the history keeps the promise. -/
def c25 : History :=
  .ofRows 3 10 0 [
    ⟨[], 0, [false, true], false⟩]

/-- Case 26 of the reading, "Solving the whole class is still only a tie".
The reading's verdict: the history breaks the promise. -/
def c26 : History :=
  .ofRows 3 10 1 [
    ⟨[], 0, [false, true], false⟩]

/-- Case 27 of the reading, "An empty class".
The reading's verdict: the history breaks the promise. -/
def c27 : History :=
  .ofRows 3 10 0 []

/-- Case 28 of the reading, "An advantage that lasts forever but begins at the cutoff".
The reading's verdict: the history breaks the promise. -/
def c28 : History :=
  .ofRows 3 10 1 [
    ⟨[], 0, [false, false, true], true⟩,
    ⟨[], 1, [false, false, true], true⟩]

/-- Case 29 of the reading, "The same lasting advantage begins immediately before the cutoff".
The reading's verdict: the history keeps the promise. -/
def c29 : History :=
  .ofRows 4 10 1 [
    ⟨[], 0, [false, false, true], true⟩,
    ⟨[], 1, [false, false, true], true⟩]

end AcornVerif.Intent.Postcondition.Cases
