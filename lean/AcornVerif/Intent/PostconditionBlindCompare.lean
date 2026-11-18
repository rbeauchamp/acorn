/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.PostconditionConsequences
import AcornVerif.Intent.PostconditionBlindReading
import AcornVerif.Intent.PostconditionBlindCases

/-!
# The record of the postcondition compared with its blind readings

The record `AcornVerif.Intent.Postcondition.postcondition` is compared here with the two second,
blind readings of the owner's words: the cases of `AcornVerif.Intent.PostconditionBlindCases` and
the record of `AcornVerif.Intent.PostconditionBlindReading`. Every verdict of the comparison is a
theorem of this module; where a reason is given for a verdict and no theorem is named for it, the
reason is argued from the definitions. How each difference was settled is in the record's
confirmation file, `lean/AcornVerif/Intent/Postcondition.md`; nothing here says which reading is the
owner's.

## The cases

A case is a history, not a trial. `Shows w h` says what it is for a trial `w` to show a history `h`:
its members are the history's, each counted once; its horizon is the stated attempt and its lapses
the stated number; its agent solves, and each member's attempts start, as the history says; reward
counts members solved; and the history's cap is the most an agent that keeps nothing of its
experience solves on an attempt, reached by some such agent. `Kept h` is the record's three promises
of the agent read on the history, and `Shows.meets_iff` proves that a trial that shows a history
meets the record exactly when the history keeps them. So the record's verdict on a case is `Kept`
of it, the same for every trial that shows it. `baseShows` proves that `base`, the record's own
model, shows the history `baseHistory`, so some trial that meets the record shows a history. No
trial is exhibited that shows a case of the reading: each verdict below is a theorem about the
history.

Every case gives each member one starting state and one outcome for all attempts after those it
lists, so the record's reading of it is decided by finitely many attempts (`kept_iff_decided`), and
each verdict is that decision, evaluated by Lean's kernel.

Each case is judged as the reading gave it: `c1_not_kept` and the theorems named like it, and
`c19_kept`, `c20_kept` and `c21_kept`. The reading and the record read the stated number in opposite
ways: the record as how many later attempts the agent may miss, the reading as how many later
attempts are promised. The 24 cases whose stated number is 10 use it, in the reading's sense, to
promise every later attempt before the stated attempt; in the record's sense ten lapses leave no
attempt room for the advantage, and the record refuses each of them by `not_kept_of_room`. To
compare what else those cases distinguish, each of the 24 is judged a second time with no lapse
allowed (`noLapse`), which is what the record asks when every later attempt is promised:
`c1_noLapse_kept` and the theorems named like it.

Read so, the record's verdict is the reading's on 19 of those 24 cases. It differs on cases 3, 25
and 29, where the advantage comes on the last attempt before the stated attempt and the reading
judged the promise kept, and on case 23, which the reading left open: the record refuses the four
for want of an attempt that has the advantage and leaves a later attempt before the stated attempt
(`late_advantage`). It differs on case 16, which the reading left open and the record refuses by
its fourth property alone (`c16_noLapse_again`). On the five cases whose stated number is not 10,
the record's verdict as given is the reading's on cases 18 and 21, on case 18 for another reason
than the reading's (`c18_room`), and differs on cases 17, 19 and 20. Case 17 fails the record's
promise of solving again (`c17_keeps`); that cases 19 and 20 differ by the reading of the stated
number alone is argued, not a theorem.

`returnsLater` is not a case of the reading. It was made for this comparison: case 16 with no lapse
allowed and the returning member solved on every attempt after those the case lists. The record
admits it (`returnsLater_kept`).

## The blind record

The blind record computes with a run, attempts, rewards and counts of its own. Its run, its solving
of a member on an attempt, its reward of an attempt and of the class, and its count of members
solved are the record's (`run_eq`, `solvedB_eq`, `attemptReturn_eq`, `classReward_eq`,
`classSolved_eq`); its sums over the attempts so far, `AcornOwnerIntent.streamReward` and
`AcornOwnerIntent.streamSolved`, have no counterpart in the record. Its first property holds of
every trial (`receivesWorldReward`). Neither record gives the other:

* `halted_mine_not_theirs`: the record admits `halted`, whose agent solves nothing from the horizon
  on, and the blind record refuses it. `halted` fails the blind record's fifth property
  (`halted_not_able`), which asks at every later attempt of the agent's life that it could still
  reach a solved member's goal.
* `hurried_theirs_not_mine`: the blind record admits `hurried`, whose agent first earns its
  advantage on the last attempt before the horizon, and the record refuses it, since that attempt
  leaves no later attempt before the horizon.

Property by property:

* Solving again. The record's property gives the blind record's (`mine_solvesAgain`), and where
  every attempt of every member starts from one state the blind record's gives the record's
  (`theirs_keeps`). Elsewhere the blind record allows the lapses anew in each stretch of attempts
  that start from one state, and the record allows them once for each member; no trial is exhibited
  that tells them apart, so that difference is stated in the confirmation file and labelled
  unproved.
* Learning again. The blind record's fifth property gives the record's fourth in a class whose
  attempts last at least a step (`theirs_learnsAgain`); `halted_not_able`, with
  `AcornVerif.Intent.Postcondition.halted_meets`, shows that the converse fails.
* The agents compared. The blind record compares the agent with every agent whose action does not
  depend on its memory, and the record with every agent whose next memory does not depend on what
  it is given. Each agent of the first kind earns what an agent of the second kind earns, so the
  record's advantage is an advantage over the blind record's agents too
  (`mine_advantage_theirs`). No trial is exhibited that meets the blind record with an agent that
  keeps nothing of its experience as the record reads that, such as a script of timed actions, and
  none is refuted: labelled unproved.
* The advantage, and the lemma on reward and members solved. The blind record reads the lemma on
  each attempt before the horizon, for two agents on the same attempt, in that attempt's reward and
  in reward summed over the attempts so far; it reads the advantage in summed reward, on every
  attempt from some attempt to the horizon. `hurried_theirs_not_mine` is the only theorem here about
  that difference, and it concerns the room after the advantage; nothing is proved here about
  summed against per-attempt reward: labelled unproved.
-/

namespace AcornVerif.Intent.Postcondition.Compare

open LeanIntent WorldInterface Cases

/-! ## The record's reading of a history -/

/-- How many attempts come before a history's stated attempt. -/
def before (h : History) : Nat := h.stated - 1

/-- How many members the learning agent solves on the attempt of index `n`. -/
def count (h : History) (n : Nat) : Nat :=
  ((List.finRange h.members).filter fun i => h.solved i n).length

/-- The record's property on the advantage, read on a history: on some attempt that leaves more
later attempts before the stated attempt than the stated number, the learning agent solves more
members than any agent that keeps nothing of its experience could on one attempt. -/
def Advantage (h : History) : Prop :=
  ∃ n, n + h.number + 1 < before h ∧ h.cap < count h n

/-- The record's property on solving again, read on a history. -/
def Keeps (h : History) : Prop :=
  ∀ i, ∃ lapsed : List Nat, lapsed.length ≤ h.number ∧
    ∀ n n', n ≤ n' → n' < before h → (∀ k, n ≤ k → k ≤ n' → h.start i k = h.start i n) →
      h.solved i n = true → n' ∉ lapsed → h.solved i n' = true

/-- The record's property on learning again, read on a history. -/
def Again (h : History) : Prop :=
  ∀ i n g n', n < g → g < n' → h.start i g ≠ h.start i n →
    (∀ k, n' ≤ k → h.start i k = h.start i n) → h.solved i n = true →
      ∃ n'', g < n'' ∧ h.solved i n'' = true

/-- The record's three promises of the agent, read on a history. -/
def Kept (h : History) : Prop :=
  Advantage h ∧ Keeps h ∧ Again h

/-- The trial `w` shows the history `h`: its members are the history's, each counted once; its
horizon is the stated attempt and its lapses the stated number; the learning agent solves, and each
member's attempts start, as the history says; reward counts members solved, as the reading was told
of every input; and the most an agent that keeps nothing of its experience solves on one attempt is
the history's cap. -/
structure Shows (w : Trial) (h : History) where
  /-- The member of the class that the history's member of index `i` is. -/
  name : Fin h.members → w.Index
  /-- Every member of the class is one the history names. -/
  every : ∀ j, ∃ i, name i = j
  /-- The comparison counts each of the history's members once. -/
  counted : w.counted = (List.finRange h.members).map name
  /-- The horizon is the stated attempt: the reading counts attempts from 1, the record from 0. -/
  horizon : w.horizon + 1 = h.stated
  /-- The lapses are the stated number. -/
  lapses : w.lapses = h.number
  /-- The learning agent solves a member on an attempt exactly when the history says so. -/
  solved : ∀ i n, w.solves w.agent (name i) n = h.solved i n
  /-- Two attempts of a member start from the same state exactly when their labels are equal. -/
  same : ∀ i n k, w.SameProblem (name i) n k ↔ h.start i k = h.start i n
  /-- Reward counts members solved. -/
  reward : rewardCountsMembers.holds w
  /-- No agent that keeps nothing of its experience solves more members on an attempt. -/
  capped : ∀ B, KeepsNothing B → ∀ k, w.solvedCount B k ≤ h.cap
  /-- Some agent that keeps nothing of its experience solves that many on some attempt. -/
  reached : ∃ B, KeepsNothing B ∧ ∃ k, w.solvedCount B k = h.cap

namespace Shows

variable {w : Trial} {h : History}

theorem horizon_eq (s : Shows w h) : w.horizon = before h := by
  have := s.horizon
  unfold before
  omega

theorem count_eq (s : Shows w h) (n : Nat) : w.solvedCount w.agent n = count h n := by
  unfold Trial.solvedCount count
  rw [s.counted, List.filter_map, List.length_map]
  congr 2
  funext i
  exact s.solved i n

theorem advantage_iff (s : Shows w h) : earnsMoreInTime.holds w ↔ Advantage h := by
  constructor
  · rintro ⟨n, room, more⟩
    obtain ⟨B, hB, k, hk⟩ := s.reached
    refine ⟨n, by rw [← s.lapses, ← s.horizon_eq]; exact room, ?_⟩
    have hlt := (s.reward w.agent B (.inl rfl) (.inr hB) n k).mp (more B hB k)
    rw [hk, s.count_eq] at hlt
    exact hlt
  · rintro ⟨n, room, more⟩
    refine ⟨n, by rw [s.lapses, s.horizon_eq]; exact room, fun B hB k => ?_⟩
    refine (s.reward w.agent B (.inl rfl) (.inr hB) n k).mpr ?_
    rw [s.count_eq]
    exact Nat.lt_of_le_of_lt (s.capped B hB k) more

theorem keeps_iff (s : Shows w h) : keepsSolving.holds w ↔ Keeps h := by
  constructor
  · intro hk i
    obtain ⟨lapsed, few, keeps⟩ := hk (s.name i)
    refine ⟨lapsed, by rw [← s.lapses]; exact few, fun n n' hle hlt same hs out => ?_⟩
    rw [← s.solved]
    exact keeps n n' hle (by rw [s.horizon_eq]; exact hlt)
      (fun k h1 h2 => (s.same i n k).mpr (same k h1 h2)) (by rw [s.solved]; exact hs) out
  · intro hk j
    obtain ⟨i, rfl⟩ := s.every j
    obtain ⟨lapsed, few, keeps⟩ := hk i
    refine ⟨lapsed, by rw [s.lapses]; exact few, fun n n' hle hlt same hs out => ?_⟩
    rw [s.solved]
    exact keeps n n' hle (by rw [← s.horizon_eq]; exact hlt)
      (fun k h1 h2 => (s.same i n k).mp (same k h1 h2)) (by rw [← s.solved]; exact hs) out

theorem again_iff (s : Shows w h) : learnsAgain.holds w ↔ Again h := by
  constructor
  · intro ha i n g n' h1 h2 left back hs
    obtain ⟨n'', late, hs'⟩ := ha (s.name i) n g n' h1 h2
      (fun same => left ((s.same i n g).mp same))
      (fun k hk => (s.same i n k).mpr (back k hk)) (by rw [s.solved]; exact hs)
    exact ⟨n'', late, by rw [← s.solved]; exact hs'⟩
  · intro ha j n g n' h1 h2 left back hs
    obtain ⟨i, rfl⟩ := s.every j
    obtain ⟨n'', late, hs'⟩ := ha i n g n' h1 h2
      (fun same => left ((s.same i n g).mpr same))
      (fun k hk => (s.same i n k).mp (back k hk)) (by rw [← s.solved]; exact hs)
    exact ⟨n'', late, by rw [s.solved]; exact hs'⟩

/-- **The record's verdict on a history.** A trial that shows a history meets the record exactly
when the history keeps the record's three promises of the agent. -/
theorem meets_iff (s : Shows w h) : postcondition.Meets w ↔ Kept h := by
  rw [postcondition_meets, s.advantage_iff, s.keeps_iff, s.again_iff]
  exact ⟨fun hm => hm.2, fun hk => ⟨s.reward, hk⟩⟩

end Shows

/-! ## Deciding the record's reading of a history that settles -/

/-- The record's promise of solving again reaches the attempt of index `n'` of the member `i`: the
learning agent solved the member on an attempt no later, and every attempt from that one to this
starts from that one's state. -/
def Owed (h : History) (i : Fin h.members) (n' : Nat) : Prop :=
  ∃ n, n ≤ n' ∧ (∀ k, k ≤ n' → n ≤ k → h.start i k = h.start i n) ∧ h.solved i n = true

instance (h : History) (i : Fin h.members) (n' : Nat) : Decidable (Owed h i n') := by
  unfold Owed
  infer_instance

/-- The attempts before the stated attempt that the promise of solving again reaches and on which
the learning agent does not solve the member. -/
def missed (h : History) (i : Fin h.members) : List Nat :=
  (List.range (before h)).filter fun n' => decide (Owed h i n') && !h.solved i n'

theorem mem_missed {h : History} {i : Fin h.members} {n' : Nat} :
    n' ∈ missed h i ↔ n' < before h ∧ Owed h i n' ∧ h.solved i n' = false := by
  simp [missed, List.mem_filter]

/-- The record's promise of solving again holds of a history exactly when, for each member, the
attempts before the stated attempt that it reaches and the agent misses are at most the stated
number. -/
theorem keeps_iff_missed (h : History) : Keeps h ↔ ∀ i, (missed h i).length ≤ h.number := by
  constructor
  · intro hk i
    obtain ⟨lapsed, few, keeps⟩ := hk i
    refine Nat.le_trans (length_le_of_injective (f := id) (fun _ _ e => e) ?_ fun n' hn' => ?_) few
    · exact (List.nodup_range).sublist List.filter_sublist
    · obtain ⟨hlt, ⟨n, hle, same, hs⟩, hmiss⟩ := mem_missed.mp hn'
      refine Decidable.byContradiction fun out => ?_
      have := keeps n n' hle hlt (fun k h1 h2 => same k h2 h1) hs out
      rw [hmiss] at this
      exact Bool.noConfusion this
  · intro hm i
    refine ⟨missed h i, hm i, fun n n' hle hlt same hs out => ?_⟩
    cases hn' : h.solved i n' with
    | true => rfl
    | false =>
      exact absurd (mem_missed.mpr ⟨hlt, ⟨n, hle, fun k h1 h2 => same k h2 h1, hs⟩, hn'⟩) out

/-- From the attempt of index `T` on, each member's attempts all start from one state and are all
solved or all not. -/
def Settled (h : History) (T : Nat) : Prop :=
  ∀ i k, T ≤ k → h.start i k = h.start i T ∧ h.solved i k = h.solved i T

/-- Every attempt of the member `i` from the one of index `n'` up to the one of index `T` starts
from the state the attempt of index `n` started from. -/
def BackBy (h : History) (T : Nat) (i : Fin h.members) (n n' : Nat) : Prop :=
  ∀ k, k ≤ T → n' ≤ k → h.start i k = h.start i n

instance (h : History) (T : Nat) (i : Fin h.members) (n n' : Nat) :
    Decidable (BackBy h T i n n') := by
  unfold BackBy
  infer_instance

/-- The member `i` is solved on an attempt after the one of index `g`, up to the one of index
`T`. -/
def SolvedBy (h : History) (T : Nat) (i : Fin h.members) (g : Nat) : Prop :=
  ∃ n'', n'' ≤ T ∧ g < n'' ∧ h.solved i n'' = true

instance (h : History) (T : Nat) (i : Fin h.members) (g : Nat) :
    Decidable (SolvedBy h T i g) := by
  unfold SolvedBy
  infer_instance

/-- The record's promise of learning again at one triple of attempts of a member, read up to the
attempt of index `T`: the solved one of index `n`, a later one of index `g` that starts from another
state, and a still later one of index `n'` from which every attempt up to `T` starts from the solved
one's state; then the member is solved on an attempt after `g`, up to `T`. -/
def AgainAt (h : History) (T : Nat) (i : Fin h.members) (n g n' : Nat) : Prop :=
  n < g → g < n' → h.start i g ≠ h.start i n → BackBy h T i n n' → h.solved i n = true →
    SolvedBy h T i g

instance (h : History) (T : Nat) (i : Fin h.members) (n g n' : Nat) :
    Decidable (AgainAt h T i n g n') := by
  unfold AgainAt
  infer_instance

/-- The record's promise of learning again, read on the attempts up to the one of index `T` of a
history that settles from it on. -/
def AgainBefore (h : History) (T : Nat) : Prop :=
  ∀ i : Fin h.members, ∀ n, n < T → ∀ g, g < T → ∀ n', n' ≤ T → AgainAt h T i n g n'

instance (h : History) (T : Nat) : Decidable (AgainBefore h T) := by
  unfold AgainBefore
  infer_instance

theorem again_iff_before {h : History} {T : Nat} (hT : Settled h T) :
    Again h ↔ AgainBefore h T := by
  constructor
  · intro ha i n _ g hg n' hn' h1 h2 left back hs
    obtain ⟨n'', late, hs'⟩ := ha i n g n' h1 h2 left (fun k hk => by
      by_cases hb : k ≤ T
      · exact back k hb hk
      · rw [(hT i k (by omega)).1]
        exact back T (Nat.le_refl _) hn') hs
    by_cases hb : n'' ≤ T
    · exact ⟨n'', hb, late, hs'⟩
    · exact ⟨T, Nat.le_refl _, hg, by rw [← (hT i n'' (by omega)).2]; exact hs'⟩
  · intro ha i n g n' h1 h2 left back hs
    have hg : g < T := Nat.lt_of_not_le fun hge => left (by
      rw [(hT i g hge).1, ← (hT i (max n' T) (Nat.le_max_right _ _)).1]
      exact back _ (Nat.le_max_left _ _))
    have hn : n < T := by omega
    by_cases hb : n' ≤ T
    · obtain ⟨n'', _, late, hs'⟩ := ha i n hn g hg n' hb h1 h2 left (fun k _ hk => back k hk) hs
      exact ⟨n'', late, hs'⟩
    · obtain ⟨n'', _, late, hs'⟩ := ha i n hn g hg T (Nat.le_refl _) h1 hg left
        (fun k hk hk' => by
          rw [show k = T by omega, ← (hT i n' (by omega)).1]
          exact back n' (Nat.le_refl _)) hs
      exact ⟨n'', late, hs'⟩

/-- What decides the record's reading of a history that settles from the attempt of index `T` on:
each part reads only attempts before the stated attempt, or up to `T`. -/
def Decided (h : History) (T : Nat) : Prop :=
  (∃ n, n < before h ∧ n + h.number + 1 < before h ∧ h.cap < count h n) ∧
    (∀ i, (missed h i).length ≤ h.number) ∧ AgainBefore h T

instance (h : History) (T : Nat) : Decidable (Decided h T) := by
  unfold Decided
  infer_instance

/-- **The record's reading of a settled history is decided by finitely many of its attempts.** -/
theorem kept_iff_decided {h : History} {T : Nat} (hT : Settled h T) : Kept h ↔ Decided h T := by
  unfold Kept Decided
  rw [keeps_iff_missed, again_iff_before hT]
  refine and_congr ⟨fun ⟨n, room, more⟩ => ⟨n, by omega, room, more⟩,
    fun ⟨n, _, room, more⟩ => ⟨n, room, more⟩⟩ Iff.rfl

/-- A history given by rows settles once every row's listed values are past. -/
theorem settled_ofRows (stated number cap : Nat) (rows : List Row) (T : Nat)
    (hT : ∀ r ∈ rows, r.starts.length ≤ T ∧ r.solved.length ≤ T) :
    Settled (History.ofRows stated number cap rows) T := by
  intro i k hk
  have hi : i.val < rows.length := i.isLt
  obtain ⟨hs, hv⟩ := hT _ (List.getElem_mem hi)
  constructor
  · show tabled (rows[i.val]'hi).starts (rows[i.val]'hi).startsLater k =
      tabled (rows[i.val]'hi).starts (rows[i.val]'hi).startsLater T
    rw [tabled_later _ _ (Nat.le_trans hs hk), tabled_later _ _ hs]
  · show tabled (rows[i.val]'hi).solved (rows[i.val]'hi).solvedLater k =
      tabled (rows[i.val]'hi).solved (rows[i.val]'hi).solvedLater T
    rw [tabled_later _ _ (Nat.le_trans hv hk), tabled_later _ _ hv]

/-! ## A history the record's own model shows -/

/-- The history of `base`, the two-door class with `finder`: both members' attempts always start
from one state; on the first attempt the agent solves the first member only, and from the second
attempt on both; an agent that keeps nothing solves one member on an attempt; the stated attempt
is the fourth and the stated number 0. -/
def baseHistory : History :=
  .ofRows 4 0 1 [⟨[], 0, [true], true⟩, ⟨[], 0, [false], true⟩]

theorem baseHistory_settled : Settled baseHistory 1 :=
  settled_ofRows _ _ _ _ 1 (by decide)

/-- The record's reading of `baseHistory`: it keeps the three promises. -/
theorem baseHistory_kept : Kept baseHistory :=
  (kept_iff_decided baseHistory_settled).mpr (by decide)

/-- **`base` shows `baseHistory`**, so the hypothesis that a trial shows a history is one that a
model of the record meets: the member the history names first is the first door's. -/
def baseShows : Shows base baseHistory where
  name := fun i => i.val == 0
  every := fun j => by
    cases j
    · exact ⟨⟨1, by decide⟩, rfl⟩
    · exact ⟨⟨0, by decide⟩, rfl⟩
  counted := rfl
  horizon := rfl
  lapses := rfl
  solved := fun i n => by
    match i, n with
    | ⟨0, _⟩, 0 => rfl
    | ⟨0, _⟩, n + 1 => exact finder_solves List.sum 1 finder true n
    | ⟨1, _⟩, 0 => rfl
    | ⟨1, _⟩, n + 1 => exact finder_solves List.sum 1 finder false n
  same := fun i n k => by
    match i with
    | ⟨0, _⟩ => exact ⟨fun _ => rfl, fun _ => doors_sameProblem List.sum 1 finder true n k⟩
    | ⟨1, _⟩ => exact ⟨fun _ => rfl, fun _ => doors_sameProblem List.sum 1 finder false n k⟩
  reward := doors_rewardCounts List.sum 1 finder fair_sum_one
  capped := fun (B : Agent (Option Bool) Bool) hB k => by
    show (doors List.sum 1 finder).solvedCount B k ≤ 1
    rw [doors_solvedCount, doors_solves, doors_solves, keepsNothing_tried 1 hB,
      keepsNothing_tried 1 hB]
    cases guess B k <;> decide
  reached := ⟨always true, always_keepsNothing true, 0, by decide⟩

/-! ## The record's verdict on each case of the cases reading

Each case is judged as the reading gave it, with its stated number read as the record reads it, the
number of attempts the agent may miss. The 24 cases whose stated number is 10 are judged a second
time with no lapse allowed (`noLapse`): the reading took that number to promise every later attempt
before the stated attempt, which is what the record asks when it allows no lapse. A history that
allows ten lapses and reads at most four attempts leaves no attempt room for the advantage, so the
record refuses each of those 24 cases as given by `not_kept_of_room`. -/

/-- The history `h` with no lapse allowed: its stated number set to 0. -/
def noLapse (h : History) : History :=
  { h with number := 0 }

theorem Settled.noLapse {h : History} {T : Nat} (hT : Settled h T) : Settled (noLapse h) T :=
  hT

/-- A history whose stated number leaves no attempt before the stated attempt with more later
attempts than it does not keep the record's promises: the advantage has no room. -/
theorem not_kept_of_room {h : History} (tight : before h ≤ h.number + 1) : ¬ Kept h :=
  fun ⟨⟨_, room, _⟩, _⟩ => by omega

/-- A history has the record's advantage exactly when some attempt before the stated attempt has
the room and the count. -/
theorem advantage_iff (h : History) :
    Advantage h ↔ ∃ n, n < before h ∧ n + h.number + 1 < before h ∧ h.cap < count h n :=
  ⟨fun ⟨n, room, more⟩ => ⟨n, by omega, room, more⟩, fun ⟨n, _, room, more⟩ => ⟨n, room, more⟩⟩

theorem c1_settled : Settled c1 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 1 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it keeps the promise. -/
theorem c1_not_kept : ¬ Kept c1 :=
  not_kept_of_room (by decide)

/-- Case 1 with no lapse allowed: the record's verdict is that the history keeps the
promise; the reading's, that it keeps the promise. -/
theorem c1_noLapse_kept : Kept (noLapse c1) :=
  (kept_iff_decided c1_settled.noLapse).mpr (by decide +kernel)

theorem c2_settled : Settled c2 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 2 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it breaks the promise. -/
theorem c2_not_kept : ¬ Kept c2 :=
  not_kept_of_room (by decide)

/-- Case 2 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it breaks the promise. -/
theorem c2_noLapse_not_kept : ¬ Kept (noLapse c2) :=
  fun h => absurd ((kept_iff_decided c2_settled.noLapse).mp h) (by decide +kernel)

theorem c3_settled : Settled c3 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 3 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it keeps the promise. -/
theorem c3_not_kept : ¬ Kept c3 :=
  not_kept_of_room (by decide)

/-- Case 3 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it keeps the promise. -/
theorem c3_noLapse_not_kept : ¬ Kept (noLapse c3) :=
  fun h => absurd ((kept_iff_decided c3_settled.noLapse).mp h) (by decide +kernel)

theorem c4_settled : Settled c4 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 4 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it breaks the promise. -/
theorem c4_not_kept : ¬ Kept c4 :=
  not_kept_of_room (by decide)

/-- Case 4 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it breaks the promise. -/
theorem c4_noLapse_not_kept : ¬ Kept (noLapse c4) :=
  fun h => absurd ((kept_iff_decided c4_settled.noLapse).mp h) (by decide +kernel)

theorem c5_settled : Settled c5 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 5 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it breaks the promise. -/
theorem c5_not_kept : ¬ Kept c5 :=
  not_kept_of_room (by decide)

/-- Case 5 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it breaks the promise. -/
theorem c5_noLapse_not_kept : ¬ Kept (noLapse c5) :=
  fun h => absurd ((kept_iff_decided c5_settled.noLapse).mp h) (by decide +kernel)

theorem c6_settled : Settled c6 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 6 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it keeps the promise. -/
theorem c6_not_kept : ¬ Kept c6 :=
  not_kept_of_room (by decide)

/-- Case 6 with no lapse allowed: the record's verdict is that the history keeps the
promise; the reading's, that it keeps the promise. -/
theorem c6_noLapse_kept : Kept (noLapse c6) :=
  (kept_iff_decided c6_settled.noLapse).mpr (by decide +kernel)

theorem c7_settled : Settled c7 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 7 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it keeps the promise. -/
theorem c7_not_kept : ¬ Kept c7 :=
  not_kept_of_room (by decide)

/-- Case 7 with no lapse allowed: the record's verdict is that the history keeps the
promise; the reading's, that it keeps the promise. -/
theorem c7_noLapse_kept : Kept (noLapse c7) :=
  (kept_iff_decided c7_settled.noLapse).mpr (by decide +kernel)

theorem c8_settled : Settled c8 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 8 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it breaks the promise. -/
theorem c8_not_kept : ¬ Kept c8 :=
  not_kept_of_room (by decide)

/-- Case 8 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it breaks the promise. -/
theorem c8_noLapse_not_kept : ¬ Kept (noLapse c8) :=
  fun h => absurd ((kept_iff_decided c8_settled.noLapse).mp h) (by decide +kernel)

theorem c9_settled : Settled c9 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 9 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it keeps the promise. -/
theorem c9_not_kept : ¬ Kept c9 :=
  not_kept_of_room (by decide)

/-- Case 9 with no lapse allowed: the record's verdict is that the history keeps the
promise; the reading's, that it keeps the promise. -/
theorem c9_noLapse_kept : Kept (noLapse c9) :=
  (kept_iff_decided c9_settled.noLapse).mpr (by decide +kernel)

theorem c10_settled : Settled c10 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 10 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it breaks the promise. -/
theorem c10_not_kept : ¬ Kept c10 :=
  not_kept_of_room (by decide)

/-- Case 10 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it breaks the promise. -/
theorem c10_noLapse_not_kept : ¬ Kept (noLapse c10) :=
  fun h => absurd ((kept_iff_decided c10_settled.noLapse).mp h) (by decide +kernel)

theorem c11_settled : Settled c11 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 11 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it keeps the promise. -/
theorem c11_not_kept : ¬ Kept c11 :=
  not_kept_of_room (by decide)

/-- Case 11 with no lapse allowed: the record's verdict is that the history keeps the
promise; the reading's, that it keeps the promise. -/
theorem c11_noLapse_kept : Kept (noLapse c11) :=
  (kept_iff_decided c11_settled.noLapse).mpr (by decide +kernel)

theorem c12_settled : Settled c12 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 12 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it breaks the promise. -/
theorem c12_not_kept : ¬ Kept c12 :=
  not_kept_of_room (by decide)

/-- Case 12 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it breaks the promise. -/
theorem c12_noLapse_not_kept : ¬ Kept (noLapse c12) :=
  fun h => absurd ((kept_iff_decided c12_settled.noLapse).mp h) (by decide +kernel)

theorem c13_settled : Settled c13 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 13 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it keeps the promise. -/
theorem c13_not_kept : ¬ Kept c13 :=
  not_kept_of_room (by decide)

/-- Case 13 with no lapse allowed: the record's verdict is that the history keeps the
promise; the reading's, that it keeps the promise. -/
theorem c13_noLapse_kept : Kept (noLapse c13) :=
  (kept_iff_decided c13_settled.noLapse).mpr (by decide +kernel)

theorem c14_settled : Settled c14 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 14 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it breaks the promise. -/
theorem c14_not_kept : ¬ Kept c14 :=
  not_kept_of_room (by decide)

/-- Case 14 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it breaks the promise. -/
theorem c14_noLapse_not_kept : ¬ Kept (noLapse c14) :=
  fun h => absurd ((kept_iff_decided c14_settled.noLapse).mp h) (by decide +kernel)

theorem c15_settled : Settled c15 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 15 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it keeps the promise. -/
theorem c15_not_kept : ¬ Kept c15 :=
  not_kept_of_room (by decide)

/-- Case 15 with no lapse allowed: the record's verdict is that the history keeps the
promise; the reading's, that it keeps the promise. -/
theorem c15_noLapse_kept : Kept (noLapse c15) :=
  (kept_iff_decided c15_settled.noLapse).mpr (by decide +kernel)

theorem c16_settled : Settled c16 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 16 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that the words do not settle it. -/
theorem c16_not_kept : ¬ Kept c16 :=
  not_kept_of_room (by decide)

/-- Case 16 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that the words do not settle it. -/
theorem c16_noLapse_not_kept : ¬ Kept (noLapse c16) :=
  fun h => absurd ((kept_iff_decided c16_settled.noLapse).mp h) (by decide +kernel)

theorem c17_settled : Settled c17 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 17 as given: the record's verdict is that the history breaks the promise; the
reading's, that it keeps the promise. -/
theorem c17_not_kept : ¬ Kept c17 :=
  fun h => absurd ((kept_iff_decided c17_settled).mp h) (by decide +kernel)

theorem c18_settled : Settled c18 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 18 as given: the record's verdict is that the history breaks the promise; the
reading's, that it breaks the promise. -/
theorem c18_not_kept : ¬ Kept c18 :=
  fun h => absurd ((kept_iff_decided c18_settled).mp h) (by decide +kernel)

theorem c19_settled : Settled c19 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 19 as given: the record's verdict is that the history keeps the promise; the
reading's, that the words do not settle it. -/
theorem c19_kept : Kept c19 :=
  (kept_iff_decided c19_settled).mpr (by decide +kernel)

theorem c20_settled : Settled c20 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 20 as given: the record's verdict is that the history keeps the promise; the
reading's, that it breaks the promise. -/
theorem c20_kept : Kept c20 :=
  (kept_iff_decided c20_settled).mpr (by decide +kernel)

theorem c21_settled : Settled c21 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 21 as given: the record's verdict is that the history keeps the promise; the
reading's, that it keeps the promise. -/
theorem c21_kept : Kept c21 :=
  (kept_iff_decided c21_settled).mpr (by decide +kernel)

theorem c22_settled : Settled c22 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 22 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it breaks the promise. -/
theorem c22_not_kept : ¬ Kept c22 :=
  not_kept_of_room (by decide)

/-- Case 22 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it breaks the promise. -/
theorem c22_noLapse_not_kept : ¬ Kept (noLapse c22) :=
  fun h => absurd ((kept_iff_decided c22_settled.noLapse).mp h) (by decide +kernel)

theorem c23_settled : Settled c23 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 23 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that the words do not settle it. -/
theorem c23_not_kept : ¬ Kept c23 :=
  not_kept_of_room (by decide)

/-- Case 23 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that the words do not settle it. -/
theorem c23_noLapse_not_kept : ¬ Kept (noLapse c23) :=
  fun h => absurd ((kept_iff_decided c23_settled.noLapse).mp h) (by decide +kernel)

theorem c24_settled : Settled c24 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 24 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it keeps the promise. -/
theorem c24_not_kept : ¬ Kept c24 :=
  not_kept_of_room (by decide)

/-- Case 24 with no lapse allowed: the record's verdict is that the history keeps the
promise; the reading's, that it keeps the promise. -/
theorem c24_noLapse_kept : Kept (noLapse c24) :=
  (kept_iff_decided c24_settled.noLapse).mpr (by decide +kernel)

theorem c25_settled : Settled c25 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 25 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it keeps the promise. -/
theorem c25_not_kept : ¬ Kept c25 :=
  not_kept_of_room (by decide)

/-- Case 25 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it keeps the promise. -/
theorem c25_noLapse_not_kept : ¬ Kept (noLapse c25) :=
  fun h => absurd ((kept_iff_decided c25_settled.noLapse).mp h) (by decide +kernel)

theorem c26_settled : Settled c26 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 26 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it breaks the promise. -/
theorem c26_not_kept : ¬ Kept c26 :=
  not_kept_of_room (by decide)

/-- Case 26 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it breaks the promise. -/
theorem c26_noLapse_not_kept : ¬ Kept (noLapse c26) :=
  fun h => absurd ((kept_iff_decided c26_settled.noLapse).mp h) (by decide +kernel)

theorem c27_settled : Settled c27 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 27 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it breaks the promise. -/
theorem c27_not_kept : ¬ Kept c27 :=
  not_kept_of_room (by decide)

/-- Case 27 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it breaks the promise. -/
theorem c27_noLapse_not_kept : ¬ Kept (noLapse c27) :=
  fun h => absurd ((kept_iff_decided c27_settled.noLapse).mp h) (by decide +kernel)

theorem c28_settled : Settled c28 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 28 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it breaks the promise. -/
theorem c28_not_kept : ¬ Kept c28 :=
  not_kept_of_room (by decide)

/-- Case 28 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it breaks the promise. -/
theorem c28_noLapse_not_kept : ¬ Kept (noLapse c28) :=
  fun h => absurd ((kept_iff_decided c28_settled.noLapse).mp h) (by decide +kernel)

theorem c29_settled : Settled c29 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- Case 29 as given: the record's verdict is that the history breaks the promise, for want of room
after ten lapses; the reading's, that it keeps the promise. -/
theorem c29_not_kept : ¬ Kept c29 :=
  not_kept_of_room (by decide)

/-- Case 29 with no lapse allowed: the record's verdict is that the history breaks the
promise; the reading's, that it keeps the promise. -/
theorem c29_noLapse_not_kept : ¬ Kept (noLapse c29) :=
  fun h => absurd ((kept_iff_decided c29_settled.noLapse).mp h) (by decide +kernel)

/-! ## Which promise the record's verdict turns on, where it differs from the reading's -/

/-- Cases 3, 23, 25 and 29 with no lapse allowed fail the record's advantage: in each, no attempt
on which the agent solves more members than an agent that keeps nothing could leaves a later attempt
before the stated attempt. -/
theorem late_advantage :
    ¬ Advantage (noLapse c3) ∧ ¬ Advantage (noLapse c23) ∧ ¬ Advantage (noLapse c25) ∧
      ¬ Advantage (noLapse c29) :=
  ⟨fun h => absurd ((advantage_iff _).mp h) (by decide +kernel),
    fun h => absurd ((advantage_iff _).mp h) (by decide +kernel),
    fun h => absurd ((advantage_iff _).mp h) (by decide +kernel),
    fun h => absurd ((advantage_iff _).mp h) (by decide +kernel)⟩

/-- Case 18 as given keeps the record's promise of solving again, with its one lapse, and fails the
record's advantage, for want of room after that lapse. The reading refused it for the missed
repeat. -/
theorem c18_room : Keeps c18 ∧ ¬ Advantage c18 :=
  ⟨(keeps_iff_missed _).mpr (by decide +kernel),
    fun h => absurd ((advantage_iff _).mp h) (by decide +kernel)⟩

/-- Case 17 as given has the record's advantage and fails its promise of solving again: with no
lapse allowed, the miss on the attempt after the solved one breaks it. The reading held that a
stated number of 0 promises nothing. -/
theorem c17_keeps : Advantage c17 ∧ ¬ Keeps c17 :=
  ⟨(advantage_iff _).mpr (by decide +kernel),
    fun h => absurd ((keeps_iff_missed _).mp h) (by decide +kernel)⟩

/-! ## The blind record's definitions are the record's

The blind record computes with a run, attempts, rewards and counts of its own. Its run, its solving,
its rewards of an attempt and its counts of members solved are the record's; its sums over the
attempts so far have no counterpart in the record. -/

/-- The blind record's run from the state and memory the record's run has reached is the record's
run continued. -/
theorem evolve_run {O A : Type} (M : Member O A) (a : Agent O A) (t : Nat) :
    ∀ k, AcornOwnerIntent.evolve M a (M.run a t).1 (M.run a t).2 k = M.run a (t + k)
  | 0 => rfl
  | k + 1 => by
    show M.next a (AcornOwnerIntent.evolve M a (M.run a t).1 (M.run a t).2 k) =
      M.next a (M.run a (t + k))
    rw [evolve_run M a t k]

theorem run_eq (t : Trial) (a : Agent t.Obs t.Act) (i : t.Index) (k : Nat) :
    AcornOwnerIntent.run t a i k = (t.member i).run a k := by
  have h := evolve_run (t.member i) a 0 k
  rw [Nat.zero_add] at h
  exact h

/-- The run the blind record's ability speaks of, from the state one attempt started from and the
memory at the start of another that started from the same state, is the agent's own run from the
second. -/
theorem ability_run (t : Trial) (i : t.Index) (n n' k : Nat) (same : t.SameProblem i n n') :
    AcornOwnerIntent.evolve (t.member i) t.agent
        (AcornOwnerIntent.run t t.agent i (n * t.length)).1
        (AcornOwnerIntent.run t t.agent i (n' * t.length)).2 k =
      (t.member i).run t.agent (t.length * n' + k) := by
  have start : ((t.member i).run t.agent (t.length * n)).1 =
      ((t.member i).run t.agent (t.length * n')).1 := same.symm
  rw [run_eq, run_eq, Nat.mul_comm n, Nat.mul_comm n', start, evolve_run]

theorem solvedB_eq (t : Trial) (a : Agent t.Obs t.Act) (i : t.Index) (n : Nat) :
    AcornOwnerIntent.solvedB t a i n = t.solves a i n := by
  unfold AcornOwnerIntent.solvedB Trial.solves Trial.attemptTimes Trial.stateAt
  rw [List.any_map]
  congr 1
  funext offset
  show (t.member i).goal (AcornOwnerIntent.run t a i (n * t.length + offset)).1 =
    (t.member i).goal ((t.member i).run a (t.length * n + offset)).1
  rw [run_eq, Nat.mul_comm]

theorem attemptReturn_eq (t : Trial) (a : Agent t.Obs t.Act) (i : t.Index) (n : Nat) :
    AcornOwnerIntent.attemptReturn t a i n = t.earned a i n := by
  unfold AcornOwnerIntent.attemptReturn Trial.earned Trial.attemptTimes Trial.stateAt
  rw [List.map_map]
  congr 2
  funext offset
  show (t.member i).reward (AcornOwnerIntent.run t a i (n * t.length + offset)).1 =
    (t.member i).reward ((t.member i).run a (t.length * n + offset)).1
  rw [run_eq, Nat.mul_comm]

theorem sumRat_eq : ∀ l : List Rat, AcornOwnerIntent.sumRat l = l.sum
  | [] => rfl
  | x :: xs => by
    show x + AcornOwnerIntent.sumRat xs = (x :: xs).sum
    rw [sumRat_eq xs, List.sum_cons]

theorem classReward_eq (t : Trial) (a : Agent t.Obs t.Act) (n : Nat) :
    AcornOwnerIntent.classReward t a n = t.classReward a n := by
  unfold AcornOwnerIntent.classReward Trial.classReward
  rw [sumRat_eq]
  congr 2
  funext i
  exact attemptReturn_eq t a i n

theorem sumNat_indicator {α : Type} (p : α → Bool) :
    ∀ l : List α, AcornOwnerIntent.sumNat (l.map fun i => if p i then 1 else 0) =
      (l.filter p).length
  | [] => rfl
  | x :: xs => by
    show (if p x then 1 else 0) + AcornOwnerIntent.sumNat (xs.map fun i => if p i then 1 else 0) =
      ((x :: xs).filter p).length
    rw [sumNat_indicator p xs, List.filter_cons]
    cases p x
    · exact Nat.zero_add _
    · exact Nat.add_comm _ _

theorem classSolved_eq (t : Trial) (a : Agent t.Obs t.Act) (n : Nat) :
    AcornOwnerIntent.classSolved t a n = t.solvedCount a n := by
  unfold AcornOwnerIntent.classSolved Trial.solvedCount
  rw [sumNat_indicator (fun i => AcornOwnerIntent.solvedB t a i n)]
  congr 2
  funext i
  exact solvedB_eq t a i n

/-- A trial meets the blind record exactly when each of its five properties holds of it. -/
theorem theirs_meets {t : Trial} :
    AcornOwnerIntent.intent.Meets t ↔
      AcornOwnerIntent.ReceivesWorldReward t ∧ AcornOwnerIntent.RewardAndSolvingAgree t ∧
        AcornOwnerIntent.EventuallyMoreRewardBeforeHorizon t ∧
        AcornOwnerIntent.SolvesAgainWithAtMostStatedLapses t ∧
        AcornOwnerIntent.KeepsAbilityToLearnAgain t := by
  constructor
  · intro hm
    have h := hm.2
    exact ⟨h _ (.head _), h _ (.tail _ (.head _)), h _ (.tail _ (.tail _ (.head _))),
      h _ (.tail _ (.tail _ (.tail _ (.head _)))),
      h _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))⟩
  · intro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨(fun d hd => nomatch hd), fun p hp => ?_⟩
    simp only [AcornOwnerIntent.intent, AcornOwnerIntent.ownerProperties, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

/-- The blind record's first property holds of every trial: its run gives the agent the reward the
member's world generates. -/
theorem receivesWorldReward (t : Trial) : AcornOwnerIntent.ReceivesWorldReward t :=
  fun _ _ _ => rfl

/-! ## What each record's property gives of the other's -/

/-- The record's promise of solving again gives the blind record's: within each stretch of attempts
that start from the state of a solved attempt, before the horizon, at most the lapses are failed. -/
theorem mine_solvesAgain {w : Trial} (keeps : keepsSolving.holds w) :
    AcornOwnerIntent.SolvesAgainWithAtMostStatedLapses w := by
  intro i first last _ before solved same
  obtain ⟨lapsed, few, kept⟩ := keeps i
  refine Nat.le_trans (length_le_of_injective (f := (first + 1 + ·))
    (fun a b (e : first + 1 + a = first + 1 + b) => by omega)
    ((List.nodup_range).sublist List.filter_sublist) fun off hoff => ?_) few
  obtain ⟨hlt, hmiss⟩ := List.mem_filter.mp hoff
  have small : off < last - first := List.mem_range.mp hlt
  refine Decidable.byContradiction fun out => ?_
  have hs := kept first (first + 1 + off) (by omega) (by omega) (fun k low high => by
    have h := same k low (by omega)
    rw [run_eq, run_eq, Nat.mul_comm k, Nat.mul_comm first] at h
    exact h) ((solvedB_eq w w.agent i first).symm.trans solved) out
  rw [solvedB_eq, hs] at hmiss
  exact absurd hmiss (by decide)

/-- Among the attempts up to one on which a condition holds, there is a first on which it holds. -/
theorem exists_first (p : Nat → Bool) :
    ∀ n, p n = true → ∃ m, m ≤ n ∧ p m = true ∧ ∀ k, k < m → p k = false := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases earlier : ∃ k, k < n ∧ p k = true
    · obtain ⟨k, hk, hp⟩ := earlier
      obtain ⟨m, hm, hpm, least⟩ := ih k hk hp
      exact ⟨m, by omega, hpm, least⟩
    · exact ⟨n, Nat.le_refl _, hn, fun k hk => by
        cases hp : p k with
        | false => rfl
        | true => exact absurd ⟨k, hk, hp⟩ earlier⟩

/-- Where every attempt of every member starts from one state, the blind record's promise of
solving again gives the record's: the two ask the same there. -/
theorem theirs_keeps {w : Trial} (same : ∀ i n k, w.SameProblem i n k)
    (theirs : AcornOwnerIntent.SolvesAgainWithAtMostStatedLapses w) : keepsSolving.holds w := by
  intro i
  by_cases ever : ∃ n, n < w.horizon ∧ w.solves w.agent i n = true
  · obtain ⟨n₀, before₀, solved₀⟩ := ever
    obtain ⟨m, hm, solved, least⟩ := exists_first (fun n => w.solves w.agent i n) n₀ solved₀
    have few := theirs i m (w.horizon - 1) (by omega) (by omega)
      ((solvedB_eq w w.agent i m).trans solved) (fun n _ _ => by
        rw [run_eq, run_eq, Nat.mul_comm n, Nat.mul_comm m]
        exact same i m n)
    refine ⟨((List.range (w.horizon - 1 - m)).filter fun off =>
        !(AcornOwnerIntent.solvedB w w.agent i (m + 1 + off))).map (m + 1 + ·),
      by rw [List.length_map]; exact few, fun n n' hle before _ hs out => ?_⟩
    have early : m ≤ n := Nat.le_of_not_lt fun h => by
      have none : w.solves w.agent i n = false := least n h
      rw [hs] at none
      exact Bool.noConfusion none
    rcases Nat.eq_or_lt_of_le (Nat.le_trans early hle) with rfl | later
    · exact solved
    · cases hn' : w.solves w.agent i n' with
      | true => rfl
      | false =>
        refine absurd (List.mem_map.mpr ⟨n' - m - 1, List.mem_filter.mpr
          ⟨List.mem_range.mpr (by omega), ?_⟩, by omega⟩) out
        rw [show m + 1 + (n' - m - 1) = n' by omega, solvedB_eq, hn']
        rfl
  · exact ⟨[], Nat.zero_le _, fun n n' hle before _ hs _ => absurd ⟨n, by omega, hs⟩ ever⟩

/-- **The blind record's kept ability gives the record's fourth property**, in a class whose
attempts last at least a step: where a member's attempts are back for good at the state of a solved
attempt, the run that the ability speaks of is the agent's own run from there, so the agent solves
the member on some later attempt. -/
theorem theirs_learnsAgain {w : Trial} (positive : 0 < w.length)
    (ability : AcornOwnerIntent.KeepsAbilityToLearnAgain w) : learnsAgain.holds w := by
  intro i n g n' h1 h2 _ back solved
  obtain ⟨k, reached⟩ := ability i n n' (by omega) ((solvedB_eq w w.agent i n).trans solved)
  have start : (AcornOwnerIntent.run w w.agent i (n * w.length)).1 =
      ((w.member i).run w.agent (w.length * n')).1 := by
    rw [run_eq, Nat.mul_comm]
    exact (back n' (Nat.le_refl _)).symm
  rw [start, run_eq, Nat.mul_comm n', evolve_run] at reached
  refine ⟨(w.length * n' + k) / w.length, Nat.lt_of_lt_of_le h2
    ((Nat.le_div_iff_mul_le positive).mpr (by rw [Nat.mul_comm]; omega)), ?_⟩
  unfold Trial.solves Trial.attemptTimes
  rw [List.any_map]
  refine List.any_eq_true.mpr ⟨(w.length * n' + k) % w.length,
    List.mem_range.mpr (Nat.mod_lt _ positive), ?_⟩
  show (w.member i).goal (w.stateAt w.agent i
    (w.length * ((w.length * n' + k) / w.length) + (w.length * n' + k) % w.length)) = true
  rw [Nat.div_add_mod]
  exact reached

/-- **The record's advantage is an advantage over every agent the blind record compares with.** An
agent whose action does not depend on its memory, which is what the blind record takes keeping no
experience to be, earns what its `shell` earns, and its `shell` keeps nothing of its experience as
the record reads that. -/
theorem mine_advantage_theirs {w : Trial} (more : earnsMoreInTime.holds w) :
    ∃ n, n + w.lapses + 1 < w.horizon ∧ ∀ b, AcornOwnerIntent.KeepsNoExperience b → ∀ k,
      AcornOwnerIntent.classReward w b k < AcornOwnerIntent.classReward w w.agent n := by
  obtain ⟨n, room, hn⟩ := more
  refine ⟨n, room, fun b hb k => ?_⟩
  rw [classReward_eq, classReward_eq, ← classReward_shell hb]
  exact hn (shell b) (shell_keepsNothing b) k

/-! ## A trial each record admits and the other refuses -/

/-- In a two-door class, an agent whose action does not depend on its memory tries one door, the
same on every attempt and in both members. -/
theorem ignoring_tried (pay : Rat) {B : Agent (Option Bool) Bool}
    (hB : AcornOwnerIntent.KeepsNoExperience B) (b : Bool) (n : Nat) :
    tried pay B b n = (B.act B.initial (none, 0)).1 := by
  unfold tried
  rw [door_ask]
  exact hB _ _ _

/-- With rewards summed and a payment of one, the reward of one attempt of a two-door class and the
members solved on it order any two outcomes alike. -/
theorem fair_one (s₁ s₂ t₁ t₂ : Bool) :
    (paid List.sum 1 t₁ + (paid List.sum 1 t₂ + 0) + 0 <
        paid List.sum 1 s₁ + (paid List.sum 1 s₂ + 0) + 0) ↔
      tally t₁ t₂ + 0 < tally s₁ s₂ + 0 := by
  cases s₁ <;> cases s₂ <;> cases t₁ <;> cases t₂ <;> decide +kernel

/-- With rewards summed and a payment of one, the reward of two attempts of a two-door class and the
members solved on them order any two outcomes alike. -/
theorem fair_two (s₁ s₂ s₃ s₄ t₁ t₂ t₃ t₄ : Bool) :
    (paid List.sum 1 t₁ + (paid List.sum 1 t₂ + 0) +
          (paid List.sum 1 t₃ + (paid List.sum 1 t₄ + 0) + 0) <
        paid List.sum 1 s₁ + (paid List.sum 1 s₂ + 0) +
          (paid List.sum 1 s₃ + (paid List.sum 1 s₄ + 0) + 0)) ↔
      tally t₁ t₂ + (tally t₃ t₄ + 0) < tally s₁ s₂ + (tally s₃ s₄ + 0) := by
  cases s₁ <;> cases s₂ <;> cases s₃ <;> cases s₄ <;> cases t₁ <;> cases t₂ <;> cases t₃ <;>
    cases t₄ <;> decide +kernel

/-- What an agent earns across `hurried` on an attempt, in the terms of the two-door class. -/
theorem hurried_reward (a : Agent (Option Bool) Bool) (n : Nat) :
    AcornOwnerIntent.classReward hurried a n =
      paid List.sum 1 ((doors List.sum 1 finder).solves a true n) +
        (paid List.sum 1 ((doors List.sum 1 finder).solves a false n) + 0) :=
  (classReward_eq hurried a n).trans (doors_classReward List.sum 1 finder a n)

/-- How many members an agent solves across `hurried` on an attempt, in the terms of the two-door
class. -/
theorem hurried_solved (a : Agent (Option Bool) Bool) (n : Nat) :
    AcornOwnerIntent.classSolved hurried a n =
      tally ((doors List.sum 1 finder).solves a true n)
        ((doors List.sum 1 finder).solves a false n) :=
  (classSolved_eq hurried a n).trans (doors_solvedCount List.sum 1 finder a n)

/-- **`hurried` meets the blind record.** Its agent first earns more than every agent whose action
does not depend on its memory on its second attempt, the last before the horizon, and the blind
record asks no room after the attempt of the advantage. -/
theorem hurried_theirs : AcornOwnerIntent.intent.Meets hurried := by
  refine theirs_meets.mpr ⟨receivesWorldReward _, ?_, ?_, ?_, ?_⟩
  · intro (a : Agent (Option Bool) Bool) (b : Agent (Option Bool) Bool) _ _ n hn
    have small : n < 2 := hn
    constructor
    · show AcornOwnerIntent.classReward hurried b n < AcornOwnerIntent.classReward hurried a n ↔
        AcornOwnerIntent.classSolved hurried b n < AcornOwnerIntent.classSolved hurried a n
      rw [hurried_reward, hurried_reward, hurried_solved, hurried_solved]
      exact fair_sum_one _ _ _ _
    · match n, small with
      | 0, _ =>
        show AcornOwnerIntent.classReward hurried b 0 + 0 <
            AcornOwnerIntent.classReward hurried a 0 + 0 ↔
          AcornOwnerIntent.classSolved hurried b 0 + 0 <
            AcornOwnerIntent.classSolved hurried a 0 + 0
        rw [hurried_reward, hurried_reward, hurried_solved, hurried_solved]
        exact fair_one _ _ _ _
      | 1, _ =>
        show AcornOwnerIntent.classReward hurried b 0 +
              (AcornOwnerIntent.classReward hurried b 1 + 0) <
            AcornOwnerIntent.classReward hurried a 0 +
              (AcornOwnerIntent.classReward hurried a 1 + 0) ↔
          AcornOwnerIntent.classSolved hurried b 0 +
              (AcornOwnerIntent.classSolved hurried b 1 + 0) <
            AcornOwnerIntent.classSolved hurried a 0 +
              (AcornOwnerIntent.classSolved hurried a 1 + 0)
        rw [hurried_reward, hurried_reward, hurried_reward, hurried_reward, hurried_solved,
          hurried_solved, hurried_solved, hurried_solved]
        exact fair_two _ _ _ _ _ _ _ _
  · refine ⟨1, show 1 < 2 by decide, fun n low high (b : Agent (Option Bool) Bool) hb => ?_⟩
    have one : n = 1 := by
      have small : n < 2 := high
      omega
    subst one
    show AcornOwnerIntent.classReward hurried b 0 +
        (AcornOwnerIntent.classReward hurried b 1 + 0) <
      AcornOwnerIntent.classReward hurried finder 0 +
        (AcornOwnerIntent.classReward hurried finder 1 + 0)
    rw [hurried_reward, hurried_reward, hurried_reward, hurried_reward, doors_solves, doors_solves,
      doors_solves, doors_solves, ignoring_tried 1 hb, ignoring_tried 1 hb, ignoring_tried 1 hb,
      ignoring_tried 1 hb, finder_solves, finder_solves]
    cases (b.act b.initial (none, 0)).1 <;> decide +kernel
  · intro (i : Bool) first last _ _ _ _
    have solved : ∀ off, AcornOwnerIntent.solvedB hurried finder i (first + 1 + off) = true :=
      fun off => (solvedB_eq hurried finder i (first + 1 + off)).trans (by
        have e : first + 1 + off = first + off + 1 := by omega
        rw [e]
        exact finder_solves List.sum 1 finder i (first + off))
    have none : ((List.range (last - first)).filter fun off =>
        !(AcornOwnerIntent.solvedB hurried finder i (first + 1 + off))) = [] :=
      List.filter_eq_nil_iff.mpr fun off _ h =>
        absurd ((congrArg (!·) (solved off)).symm.trans h) (by decide)
    exact Nat.le_of_eq (congrArg List.length none)
  · intro (i : Bool) first later order _
    obtain ⟨l, rfl⟩ : ∃ l, later = l + 1 := ⟨later - 1, by omega⟩
    have same : hurried.SameProblem i first (l + 1) :=
      doors_sameProblem List.sum 1 finder i first (l + 1)
    have hit : (door 1 i).goal ((door 1 i).run finder (2 * (l + 1) + 1)).1 = true := by
      have hs := finder_solves List.sum 1 finder i l
      rw [doors_solves] at hs
      rw [door_tried, hs]
      rfl
    exact ⟨1, (congrArg (fun c : (hurried.member i).State × hurried.agent.Memory =>
      (hurried.member i).goal c.1) (ability_run hurried i first (l + 1) 1 same)).trans hit⟩

/-- **The blind record admits `hurried` and the record refuses it.** -/
theorem hurried_theirs_not_mine :
    AcornOwnerIntent.intent.Meets hurried ∧ ¬ postcondition.Meets hurried :=
  ⟨hurried_theirs, hurried_fails⟩

/-- From its fourth attempt on, the run of `halts` in the first member of the two-door class is
never at the member's goal. -/
theorem halts_never (k : Nat) :
    (door 1 true).goal ((door 1 true).run halts (2 * 3 + k)).1 = false := by
  obtain ⟨j, even | odd⟩ : ∃ j, k = 2 * j ∨ k = 2 * j + 1 := ⟨k / 2, by omega⟩
  · rw [show 2 * 3 + k = 2 * (j + 3) by omega, door_ask]
    rfl
  · rw [show 2 * 3 + k = 2 * (j + 3) + 1 by omega, door_tried, halts_other]
    rfl

/-- **`halted` fails the blind record's fifth property.** Its agent solves no member from the
horizon on, so from its fourth attempt it never reaches the first member's goal again, which that
property asks to be possible at every later attempt. -/
theorem halted_not_able : ¬ AcornOwnerIntent.KeepsAbilityToLearnAgain halted := by
  intro ability
  obtain ⟨k, reached⟩ := ability true 1 3 (by decide)
    ((solvedB_eq halted halts true 1).trans (halts_hits List.sum 1 halts true).1)
  have same : halted.SameProblem true 1 3 := doors_sameProblem List.sum 1 halts true 1 3
  have reached' : (door 1 true).goal ((door 1 true).run halts (2 * 3 + k)).1 = true :=
    (congrArg (fun c : (halted.member true).State × halted.agent.Memory =>
      (halted.member true).goal c.1) (ability_run halted true 1 3 k same)).symm.trans reached
  exact Bool.noConfusion ((halts_never k).symm.trans reached')

/-- **The record admits `halted` and the blind record refuses it.** -/
theorem halted_mine_not_theirs :
    postcondition.Meets halted ∧ ¬ AcornOwnerIntent.intent.Meets halted :=
  ⟨halted_meets, fun hm => halted_not_able (theirs_meets.mp hm).2.2.2.2⟩

/-! ## The member that leaves and returns

Case 16 is the one case of the reading in which a member's attempts leave the state of a solved
attempt and come back to it. With no lapse allowed the record refuses it by its fourth property
alone: the member is back for good from its fourth attempt and never solved again. The reading left
it open. The history `returnsLater` is not the reading's: it was made while the two forms of the
record's fourth property were compared. It is case 16 with no lapse allowed and the returning member
solved on every attempt after the four the case lists, so that it is missed on the first attempt
back and first solved again on the stated attempt itself. The record admits it. -/

/-- Case 16 with no lapse allowed has the record's advantage and its promise of solving again, and
fails its promise of learning again. -/
theorem c16_noLapse_again :
    Advantage (noLapse c16) ∧ Keeps (noLapse c16) ∧ ¬ Again (noLapse c16) :=
  ⟨(advantage_iff _).mpr (by decide +kernel), (keeps_iff_missed _).mpr (by decide +kernel),
    fun h => absurd ((again_iff_before c16_settled.noLapse).mp h) (by decide +kernel)⟩

/-- A history made for this comparison, not a case of the reading: case 16 with the stated number 0
and the returning member solved on every attempt after the four that case lists. -/
def returnsLater : History :=
  .ofRows 5 0 1 [
    ⟨[], 0, [false, true, true, true], false⟩,
    ⟨[1, 1, 3, 1], 1, [false, true, false, false], true⟩]

theorem returnsLater_settled : Settled returnsLater 5 :=
  settled_ofRows _ _ _ _ 5 (by decide)

/-- The record admits `returnsLater`: its fourth property names no attempt by which the member is
solved again, so a member first solved again on the stated attempt has it. -/
theorem returnsLater_kept : Kept returnsLater :=
  (kept_iff_decided returnsLater_settled).mpr (by decide +kernel)

end AcornVerif.Intent.Postcondition.Compare
