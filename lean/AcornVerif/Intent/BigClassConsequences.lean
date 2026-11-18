/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.BigClass
import AcornVerif.Intent.PostconditionConsequences
import AcornVerif.Intent.WorldInterfaceConsequences

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

/-! ## Continued learning pays -/

/-- An agent solves a member on an attempt exactly when its run in the member is in a state that
meets the goal at some time of the attempt. -/
theorem solves_iff (w : Trial) (A : Agent w.Obs w.Act) (i : w.Index) (n : Nat) :
    w.solves A i n = true ↔
      ∃ j, j < w.length ∧ (w.member i).goal (w.stateAt A i (w.length * n + j)) = true := by
  simp only [Trial.solves, Trial.attemptTimes, List.any_eq_true, List.mem_map, List.mem_range]
  constructor
  · intro ⟨t, ⟨j, hj, hjt⟩, hg⟩
    exact ⟨j, hj, hjt ▸ hg⟩
  · intro ⟨j, hj, hg⟩
    exact ⟨_, ⟨j, hj, rfl⟩, hg⟩

section Seeker

variable {Obs Act : Type}

/-- The state the member `M`'s world is in after `j` steps from the state `s` in which the plan `l`
is followed, action by action, and the action `a` is taken once the plan is spent. -/
def follow (M : Member Obs Act) (a : Act) : M.State → List Act → Nat → M.State
  | s, _, 0 => s
  | s, [], j + 1 => follow M a (M.step s a) [] j
  | s, x :: l, j + 1 => follow M a (M.step s x) l j

/-- One more step of following a plan takes the plan's next action, or `a` once it is spent. -/
theorem follow_succ (M : Member Obs Act) (a : Act) :
    ∀ (j : Nat) (s : M.State) (l : List Act),
      follow M a s l (j + 1) = M.step (follow M a s l j) (l.getD j a)
  | 0, _, [] => rfl
  | 0, _, _ :: _ => rfl
  | j + 1, s, [] => follow_succ M a j (M.step s a) []
  | j + 1, s, x :: l => follow_succ M a j (M.step s x) l

/-- Following a plan for as many steps as it has actions reaches the state after its actions. -/
theorem follow_length (M : Member Obs Act) (a : Act) :
    ∀ (l : List Act) (s : M.State), follow M a s l l.length = afterActions M s l
  | [], _ => rfl
  | x :: l, s => follow_length M a l (M.step s x)

/-- What the seeker knows after a step: the attempt it already marked, or, when it has marked none
and the signal says the goal is met, the attempt it is in. -/
def marked (length : Nat) (signal : Obs × Rat → Bool) (m : Nat × Option Nat) (o : Obs × Rat) :
    Option Nat :=
  match m.2 with
  | some p => some p
  | none => bif signal o then some (m.1 / length) else none

/-- The agent that tries one plan on each attempt, in the order `plans` gives them, until the
signal says a goal is met, and from then on follows the plan of the attempt on which that happened.
Its memory is the number of steps it has taken and the attempt it has marked, if any. It takes the
action `a` once a plan is spent. -/
def seeker (length : Nat) (plans : Nat → List Act) (signal : Obs × Rat → Bool) (a : Act) :
    Agent Obs Act where
  Memory := Nat × Option Nat
  initial := (0, none)
  act := fun m o =>
    ((plans ((marked length signal m o).getD (m.1 / length))).getD (m.1 % length) a,
      (m.1 + 1, marked length signal m o))

variable (M : Member Obs Act) (length : Nat) (plans : Nat → List Act)
  (signal : Obs × Rat → Bool) (a : Act)

/-- After `t` steps of its run in any member, the seeker has counted `t` steps. -/
theorem seeker_clock : ∀ t, ((M.run (seeker length plans signal a) t).2).1 = t
  | 0 => rfl
  | t + 1 => congrArg (· + 1) (seeker_clock t)

/-- What the seeker has marked after one more step of its run. -/
theorem seeker_marked (t : Nat) :
    ((M.run (seeker length plans signal a) (t + 1)).2).2 =
      marked length signal (M.run (seeker length plans signal a) t).2
        (given M (seeker length plans signal a) t) :=
  rfl

/-- The state the member is in after one more step of the seeker's run: the seeker takes the action
its current plan has for this step of the attempt. -/
theorem seeker_state (t : Nat) :
    (M.run (seeker length plans signal a) (t + 1)).1 =
      M.step (M.run (seeker length plans signal a) t).1
        ((plans (((M.run (seeker length plans signal a) (t + 1)).2).2.getD (t / length))).getD
          (t % length) a) := by
  have h := seeker_clock M length plans signal a t
  show M.step _ ((plans ((marked length signal (M.run (seeker length plans signal a) t).2
      (given M (seeker length plans signal a) t)).getD
        ((M.run (seeker length plans signal a) t).2.1 / length))).getD
          ((M.run (seeker length plans signal a) t).2.1 % length) a) = _
  rw [h]
  rfl

/-- Once the seeker has marked an attempt it keeps that mark. -/
theorem seeker_keeps (t p : Nat)
    (h : ((M.run (seeker length plans signal a) t).2).2 = some p) :
    ∀ d, ((M.run (seeker length plans signal a) (t + d)).2).2 = some p
  | 0 => h
  | d + 1 => by
    have ih := seeker_keeps t p h d
    show ((M.run (seeker length plans signal a) (t + d + 1)).2).2 = some p
    rw [seeker_marked]
    unfold marked
    rw [ih]

/-- A mark the seeker makes at a step is the attempt of that step, made because the signal said the
goal was met there. -/
theorem seeker_marks (t q : Nat)
    (h : ((M.run (seeker length plans signal a) t).2).2 = none)
    (h' : ((M.run (seeker length plans signal a) (t + 1)).2).2 = some q) :
    signal (given M (seeker length plans signal a) t) = true ∧ q = t / length := by
  rw [seeker_marked] at h'
  unfold marked at h'
  rw [h] at h'
  have hc := seeker_clock M length plans signal a t
  cases hs : signal (given M (seeker length plans signal a) t)
  · rw [hs] at h'
    exact nomatch (h' : (none : Option Nat) = some q)
  · rw [hs] at h'
    exact ⟨rfl, by rw [← hc]; exact (Option.some.inj h').symm⟩

/-- Where the signal says the goal is met at a step, the seeker has a mark after it. -/
theorem seeker_marks_success (t : Nat)
    (h : signal (given M (seeker length plans signal a) t) = true) :
    ∃ p, ((M.run (seeker length plans signal a) (t + 1)).2).2 = some p := by
  rw [seeker_marked]
  unfold marked
  cases hm : ((M.run (seeker length plans signal a) t).2).2
  · exact ⟨_, by rw [h]; rfl⟩
  · exact ⟨_, rfl⟩

/-- Following a plan for no step leaves the state as it is. -/
theorem follow_zero (s : M.State) (l : List Act) : follow M a s l 0 = s := by
  cases l <;> rfl

/-- A mark the seeker holds after some steps and did not hold before them was made at one of
them. -/
theorem seeker_first_mark (t q : Nat)
    (h : ((M.run (seeker length plans signal a) t).2).2 = none) :
    ∀ d, ((M.run (seeker length plans signal a) (t + d)).2).2 = some q →
      ∃ j, j < d ∧ ((M.run (seeker length plans signal a) (t + j)).2).2 = none ∧
        ((M.run (seeker length plans signal a) (t + j + 1)).2).2 = some q
  | 0, h' => nomatch h.symm.trans h'
  | d + 1, h' => by
    cases hm : ((M.run (seeker length plans signal a) (t + d)).2).2 with
    | none => exact ⟨d, Nat.lt_succ_self d, hm, h'⟩
    | some p =>
      have hk : ((M.run (seeker length plans signal a) (t + (d + 1))).2).2 = some p :=
        seeker_keeps M length plans signal a (t + d) p hm 1
      have hpq : p = q := Option.some.inj (hk.symm.trans h')
      obtain ⟨j, hj, hjn, hjs⟩ := seeker_first_mark t q h d (hpq ▸ hm)
      exact ⟨j, Nat.lt_succ_of_lt hj, hjn, hjs⟩

/-- Within an attempt the seeker's mark is the one it began the attempt with, or, where it began
with none, the attempt itself. -/
theorem seeker_within (hL : 0 < length) (n : Nat) :
    ∀ j, j ≤ length →
      ((M.run (seeker length plans signal a) (length * n + j)).2).2 =
          ((M.run (seeker length plans signal a) (length * n)).2).2 ∨
        (((M.run (seeker length plans signal a) (length * n)).2).2 = none ∧
          ((M.run (seeker length plans signal a) (length * n + j)).2).2 = some n)
  | 0, _ => Or.inl rfl
  | j + 1, hj => by
    have ih := seeker_within hL n j (Nat.le_of_succ_le hj)
    cases hm : ((M.run (seeker length plans signal a) (length * n + j)).2).2 with
    | some p =>
      have hk : ((M.run (seeker length plans signal a) (length * n + (j + 1))).2).2 = some p :=
        seeker_keeps M length plans signal a (length * n + j) p hm 1
      rw [hm] at ih
      rw [hk]
      exact ih
    | none =>
      rw [hm] at ih
      have h0 : ((M.run (seeker length plans signal a) (length * n)).2).2 = none := by
        rcases ih with h | ⟨_, h⟩
        · exact h.symm
        · exact nomatch h
      cases hq : ((M.run (seeker length plans signal a) (length * n + (j + 1))).2).2 with
      | none => exact Or.inl h0.symm
      | some q =>
        have hs := seeker_marks M length plans signal a (length * n + j) q hm hq
        have hdiv : (length * n + j) / length = n := by
          rw [Nat.mul_add_div hL, Nat.div_eq_of_lt (Nat.lt_of_succ_le hj), Nat.add_zero]
        exact Or.inr ⟨h0, by rw [hs.2, hdiv]⟩

/-- Throughout an attempt the seeker follows one plan: that of the attempt it began the attempt
having marked, or, where it had marked none, that of the attempt itself. -/
theorem seeker_plan (hL : 0 < length) (n j : Nat) (hj : j < length) :
    (((M.run (seeker length plans signal a) (length * n + j + 1)).2).2).getD n =
      (((M.run (seeker length plans signal a) (length * n)).2).2).getD n := by
  rcases seeker_within M length plans signal a hL n (j + 1) hj with h | ⟨h0, h⟩
  · exact congrArg (·.getD n) h
  · exact (congrArg (·.getD n) h).trans (congrArg (·.getD n) h0).symm

/-- In an attempt that starts from the member's start, the member is, after each step of the
attempt, in the state the seeker's plan for that attempt leads to. -/
theorem seeker_follows (hL : 0 < length) (n : Nat)
    (hstart : (M.run (seeker length plans signal a) (length * n)).1 = M.start) :
    ∀ j, j ≤ length →
      (M.run (seeker length plans signal a) (length * n + j)).1 =
        follow M a M.start
          (plans ((((M.run (seeker length plans signal a) (length * n)).2).2).getD n)) j
  | 0, _ => hstart.trans (follow_zero M a _ _).symm
  | j + 1, hj => by
    have ih := seeker_follows hL n hstart j (Nat.le_of_succ_le hj)
    have hlt : j < length := Nat.lt_of_succ_le hj
    have hdiv : (length * n + j) / length = n := by
      rw [Nat.mul_add_div hL, Nat.div_eq_of_lt hlt, Nat.add_zero]
    have hmod : (length * n + j) % length = j := by
      rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
    show (M.run (seeker length plans signal a) (length * n + j + 1)).1 = _
    rw [seeker_state, hdiv, hmod, seeker_plan M length plans signal a hL n j hlt, ih, follow_succ]

/-- Where every attempt of the seeker's run in a member starts from the member's start, the signal
says at every time of that run whether the member's goal is met, and the plan of attempt `m`
reaches the goal from the start in fewer actions than an attempt has steps, the seeker's run meets
the goal at some time of every attempt after `m`. -/
theorem seeker_solves (hL : 0 < length) (m : Nat)
    (hrecur : ∀ n, (M.run (seeker length plans signal a) (length * n)).1 = M.start)
    (hsignal : ∀ t, signal (given M (seeker length plans signal a) t) =
      M.goal (M.run (seeker length plans signal a) t).1)
    (hlen : (plans m).length < length)
    (hgoal : M.goal (afterActions M M.start (plans m)) = true) :
    ∀ n, m < n →
      ∃ j, j < length ∧ M.goal (M.run (seeker length plans signal a) (length * n + j)).1 = true := by
  have inv : ∀ n p, ((M.run (seeker length plans signal a) (length * n)).2).2 = some p →
      ∃ j, j < length ∧ M.goal (follow M a M.start (plans p) j) = true := by
    intro n
    induction n with
    | zero =>
      intro p h
      exact nomatch (h : (none : Option Nat) = some p)
    | succ n ih =>
      intro p h
      have h' : ((M.run (seeker length plans signal a) (length * n + length)).2).2 = some p := h
      rcases seeker_within M length plans signal a hL n length (Nat.le_refl _) with hw | ⟨h0, hw⟩
      · exact ih p (hw.symm.trans h')
      · have hp : n = p := Option.some.inj (hw.symm.trans h')
        obtain ⟨j, hj, hjn, hjs⟩ :=
          seeker_first_mark M length plans signal a (length * n) n h0 length hw
        have hs := (seeker_marks M length plans signal a (length * n + j) n hjn hjs).1
        rw [hsignal, seeker_follows M length plans signal a hL n (hrecur n) j (Nat.le_of_lt hj),
          h0] at hs
        have hs' : M.goal (follow M a M.start (plans n) j) = true := hs
        exact ⟨j, hj, hp ▸ hs'⟩
  have prog : ∃ p,
      ((M.run (seeker length plans signal a) (length * m + length)).2).2 = some p := by
    cases hmark : ((M.run (seeker length plans signal a) (length * m)).2).2 with
    | some p => exact ⟨p, seeker_keeps M length plans signal a (length * m) p hmark length⟩
    | none =>
      have hst := seeker_follows M length plans signal a hL m (hrecur m) (plans m).length
        (Nat.le_of_lt hlen)
      rw [hmark] at hst
      have hst' : (M.run (seeker length plans signal a) (length * m + (plans m).length)).1 =
          afterActions M M.start (plans m) := hst.trans (follow_length M a (plans m) M.start)
      have hsig : signal (given M (seeker length plans signal a)
          (length * m + (plans m).length)) = true := by
        rw [hsignal, hst']
        exact hgoal
      obtain ⟨p, hp⟩ := seeker_marks_success M length plans signal a _ hsig
      have hk := seeker_keeps M length plans signal a (length * m + (plans m).length + 1) p hp
        (length - ((plans m).length + 1))
      have he : length * m + (plans m).length + 1 + (length - ((plans m).length + 1)) =
          length * m + length := by omega
      rw [he] at hk
      exact ⟨p, hk⟩
  intro n hn
  obtain ⟨p, hp⟩ := prog
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hn
  have hpn : ((M.run (seeker length plans signal a) (length * n)).2).2 = some p := by
    have hk := seeker_keeps M length plans signal a (length * m + length) p hp (length * d)
    have he : length * n = length * m + length + length * d := by
      rw [hd]
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    rw [he]
    exact hk
  obtain ⟨j, hj, hg⟩ := inv n p hpn
  refine ⟨j, hj, ?_⟩
  rw [seeker_follows M length plans signal a hL n (hrecur n) j (Nat.le_of_lt hj), hpn]
  exact hg

end Seeker

/-- **Continued learning pays.** In a class that meets the record, some agent solves every counted
member on every attempt from their count on, and so more of them than any agent that keeps nothing
of its experience solves on any attempt. The agent is a seeker: attempt by attempt it tries a way to
one counted member's goal, and it keeps to the way it was following when its percept first showed
success. -/
def learningPays : Consequence Trial :=
  ⟨"some agent solves every counted member on every attempt from their count on, more than any \
    agent that keeps nothing of its experience solves on any attempt", .entailment, fun w =>
    ∃ A : Agent w.Obs w.Act, ∀ n, w.counted.length ≤ n →
      (∀ i ∈ w.counted, w.solves A i n = true) ∧
        ∀ B : Agent w.Obs w.Act, KeepsNothing B → ∀ k, w.solvedCount B k < w.solvedCount A n⟩

theorem learningPays_holds : learningPays.HoldsOf bigClass := by
  intro w hw
  obtain ⟨hreach, _, ⟨k, hk, hfrozen⟩, ⟨signal, hsignal⟩, hrecur⟩ := bigClass_meets.mp hw
  have first : w.Index := w.counted[0]'(Nat.lt_of_le_of_lt (Nat.zero_le k) hk)
  have a : w.Act :=
    (w.agent.act w.agent.initial ((w.member first).observe (w.member first).start, 0)).1
  have hplan : ∀ i : w.Index, ∃ acts : List w.Act, acts.length < w.length ∧
      (w.member i).goal (afterActions (w.member i) (w.member i).start acts) = true := by
    intro i
    obtain ⟨acts, hlen, hg⟩ := hreach (always a) i 0
    have hs : w.stateAt (always a) i (w.length * 0) = (w.member i).start := hrecur (always a) i 0
    rw [hs] at hg
    exact ⟨acts, hlen, hg⟩
  let acts : w.Index → List w.Act := fun i => Classical.choose (hplan i)
  have hacts : ∀ i, (acts i).length < w.length ∧
      (w.member i).goal (afterActions (w.member i) (w.member i).start (acts i)) = true :=
    fun i => Classical.choose_spec (hplan i)
  let plans : Nat → List w.Act := fun m => ((w.counted[m]?).map acts).getD []
  refine ⟨seeker w.length plans signal a, fun n hn => ?_⟩
  have hall : ∀ i ∈ w.counted, w.solves (seeker w.length plans signal a) i n = true := by
    intro i hi
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hi
    have hmlt : m < w.counted.length := (List.getElem?_eq_some_iff.mp hm).1
    have hpm : plans m = acts i := by
      show ((w.counted[m]?).map acts).getD [] = acts i
      rw [hm]
      rfl
    have hL : 0 < w.length := Nat.lt_of_le_of_lt (Nat.zero_le _) (hacts i).1
    obtain ⟨j, hj, hg⟩ := seeker_solves (w.member i) w.length plans signal a hL m
      (fun n => hrecur (seeker w.length plans signal a) i n)
      (fun t => hsignal (seeker w.length plans signal a) i t)
      (by rw [hpm]; exact (hacts i).1) (by rw [hpm]; exact (hacts i).2) n
      (Nat.lt_of_lt_of_le hmlt hn)
    exact (solves_iff w (seeker w.length plans signal a) i n).mpr ⟨j, hj, hg⟩
  refine ⟨hall, fun B hB k' => ?_⟩
  have hcount : w.solvedCount (seeker w.length plans signal a) n = w.counted.length := by
    show (w.counted.filter fun i => w.solves (seeker w.length plans signal a) i n).length = _
    rw [List.filter_eq_self.mpr hall]
  rw [hcount]
  exact Nat.lt_of_le_of_lt (hfrozen B hB k') hk

/-! ## An agent that starts every attempt afresh -/

/-- Where an agent's run in a member is, after some steps, where it began, the run repeats from
there. -/
theorem run_repeats {Obs Act : Type} (M : Member Obs Act) (A : Agent Obs Act) (t : Nat)
    (h : M.run A t = M.run A 0) : ∀ j, M.run A (t + j) = M.run A j
  | 0 => h
  | j + 1 => congrArg (M.next A) (run_repeats M A t h j)

/-- **An agent that starts every attempt afresh does no better than on its first.** In a class that
meets the record, an agent that begins every attempt with the memory it began its run with,
whatever it keeps within an attempt, solves on every attempt at most the number of counted members
that bounds what an agent that keeps nothing of its experience solves. -/
def freshStartsSmall : Consequence Trial :=
  ⟨"an agent that begins every attempt with the memory it began its run with solves, on every \
    attempt, at most a number of the counted members that is smaller than their count",
    .entailment, fun w =>
    ∃ k, k < w.counted.length ∧ ∀ A : Agent w.Obs w.Act,
      (∀ i n, ((w.member i).run A (w.length * n)).2 = A.initial) → ∀ n, w.solvedCount A n ≤ k⟩

theorem freshStartsSmall_holds : freshStartsSmall.HoldsOf bigClass := by
  intro w hw
  obtain ⟨k, hk, hfirst⟩ := firstAttemptSmall_holds w hw
  have hrecur := (bigClass_meets.mp hw).2.2.2.2
  refine ⟨k, hk, fun A hfresh n => ?_⟩
  have hsame : ∀ i, w.solves A i n = w.solves A i 0 := by
    intro i
    have hrun : ∀ j, (w.member i).run A (w.length * n + j) = (w.member i).run A j :=
      run_repeats (w.member i) A (w.length * n) (Prod.ext (hrecur A i n) (hfresh i n))
    have hstate : ∀ j, w.stateAt A i (w.length * n + j) = w.stateAt A i (w.length * 0 + j) := by
      intro j
      show ((w.member i).run A (w.length * n + j)).1 = ((w.member i).run A (w.length * 0 + j)).1
      rw [hrun j, Nat.mul_zero, Nat.zero_add]
    apply Bool.eq_iff_iff.mpr
    rw [solves_iff, solves_iff]
    constructor
    · intro ⟨j, hj, hg⟩
      exact ⟨j, hj, hstate j ▸ hg⟩
    · intro ⟨j, hj, hg⟩
      exact ⟨j, hj, (hstate j).symm ▸ hg⟩
  have hfun : (fun i => w.solves A i n) = fun i => w.solves A i 0 := funext hsame
  have hcount : w.solvedCount A n = w.solvedCount A 0 := by
    show (w.counted.filter fun i => w.solves A i n).length =
      (w.counted.filter fun i => w.solves A i 0).length
    rw [hfun]
  rw [hcount]
  exact hfirst A

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

/-! ## A class that counts two of its members -/

/-- The door of the member `i` of the lopsided class: the second door for the member 1, and the
first for every other member. -/
def lopsidedDoor (i : Nat) : Bool := i != 1

/-- The lopsided class: one two-door member for each natural number, all with the first door but
the member 1, of which it counts the members 0 and 1. Its attempts, its rewards, its horizon, its
lapses and its agent are those of `base`. -/
def lopsided : Trial where
  Obs := Option Bool
  Act := Bool
  Index := Nat
  member := fun i => door 1 (lopsidedDoor i)
  counted := [0, 1]
  length := 2
  total := List.sum
  horizon := 3
  lapses := 0
  agent := finder

/-- An agent solves a member of the lopsided class on an attempt exactly when the door it tries is
the member's. -/
theorem lopsided_solves (A : Agent (Option Bool) Bool) (i n : Nat) :
    lopsided.solves A i n = (tried 1 A (lopsidedDoor i) n == lopsidedDoor i) := by
  show ((door 1 (lopsidedDoor i)).goal ((door 1 (lopsidedDoor i)).run A (2 * n)).1 ||
    ((door 1 (lopsidedDoor i)).goal ((door 1 (lopsidedDoor i)).run A (2 * n + 1)).1 || false)) = _
  rw [door_tried, door_ask]
  cases tried 1 A (lopsidedDoor i) n == lopsidedDoor i <;> rfl

theorem lopsided_goalsReachable : goalsReachable.holds lopsided :=
  fun (A : Agent (Option Bool) Bool) (i : Nat) n => ⟨[lopsidedDoor i], Nat.lt_succ_self 1, by
    show (door 1 (lopsidedDoor i)).goal (afterActions (door 1 (lopsidedDoor i))
      ((door 1 (lopsidedDoor i)).run A (2 * n)).1 [lopsidedDoor i]) = true
    rw [door_ask]
    cases lopsidedDoor i <;> rfl⟩

theorem lopsided_goalsConcealed : goalsConcealed.holds lopsided :=
  ⟨wall, fun (A : Agent (Option Bool) Bool) (i : Nat) t h => by
    have hs : (door 1 (lopsidedDoor i)).goal ((door 1 (lopsidedDoor i)).run A t).1 = false :=
      h t (Nat.le_refl t)
    show ((door 1 (lopsidedDoor i)).observe ((door 1 (lopsidedDoor i)).run A t).1,
      (door 1 (lopsidedDoor i)).reward ((door 1 (lopsidedDoor i)).run A t).1) =
        (wall.observe (wall.run A t).1, wall.reward (wall.run A t).1)
    rw [← door_run_wall 1 (lopsidedDoor i) A t h]
    generalize ((door 1 (lopsidedDoor i)).run A t).1 = s at hs
    cases s with
    | ask => rfl
    | hit =>
      have hf : true = false := hs
      exact Bool.noConfusion hf
    | miss => rfl⟩

theorem lopsided_frozenShareSmall : frozenShareSmall.holds lopsided :=
  ⟨1, Nat.lt_succ_self 1, fun (B : Agent (Option Bool) Bool) hB n => by
    have h0 : lopsided.solves B (0 : Nat) n = (guess B n == true) := by
      rw [lopsided_solves, keepsNothing_tried 1 hB]
      rfl
    have h1 : lopsided.solves B (1 : Nat) n = (guess B n == false) := by
      rw [lopsided_solves, keepsNothing_tried 1 hB]
      rfl
    have hc : lopsided.solvedCount B n =
        tally (lopsided.solves B (0 : Nat) n) (lopsided.solves B (1 : Nat) n) := by
      show (([0, 1] : List Nat).filter fun i => lopsided.solves B i n).length = _
      cases h1 : lopsided.solves B (0 : Nat) n <;>
        cases h2 : lopsided.solves B (1 : Nat) n <;> simp only [List.filter, h1, h2] <;> rfl
    rw [hc, h0, h1]
    cases guess B n <;> decide⟩

theorem lopsided_successShows : successShows.holds lopsided :=
  ⟨fun (o : Option Bool × Rat) => o.1 == some true,
    fun (A : Agent (Option Bool) Bool) (i : Nat) t => by
    show ((door 1 (lopsidedDoor i)).observe ((door 1 (lopsidedDoor i)).run A t).1 == some true) =
      (door 1 (lopsidedDoor i)).goal ((door 1 (lopsidedDoor i)).run A t).1
    generalize ((door 1 (lopsidedDoor i)).run A t).1 = s
    cases s <;> rfl⟩

theorem lopsided_attemptsRecur : attemptsRecur.holds lopsided :=
  fun (A : Agent (Option Bool) Bool) (i : Nat) n => door_ask 1 (lopsidedDoor i) A n

/-- **The lopsided class meets the record.** -/
theorem lopsided_big : bigClass.Meets lopsided :=
  bigClass_meets.mpr ⟨lopsided_goalsReachable, lopsided_goalsConcealed, lopsided_frozenShareSmall,
    lopsided_successShows, lopsided_attemptsRecur⟩

/-- In the lopsided class the agent that always tries the first door, which keeps nothing of its
experience, solves every member but the member 1 on every attempt. -/
theorem lopsided_always (i n : Nat) (h : i ≠ 1) :
    lopsided.solves (always true : Agent (Option Bool) Bool) i n = true := by
  rw [lopsided_solves]
  have hd : lopsidedDoor i = true := by
    show (i != 1) = true
    exact bne_iff_ne.mpr h
  rw [hd]
  rfl

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

/-! ## The explanation -/

/-- The record explained in plain words, with its restatement standing as confirmed by the owner: the
owner confirmed contract 2's seven sentences, and that this revision carries what it states of them
is the agents' judgment, on which the owners' log attaches the owner's answer. Every consequence it
shows is recorded as derived from that restatement. The consequences decided on the owner's behalf
are recorded, with their reasons, in the record's confirmation file,
`lean/AcornVerif/Intent/BigClass.md`, and are not shown here. Each statement's freedom says what
that statement leaves open on its own subject; the shape's says what the whole record leaves
open. -/
def bigClassExplained : Explanation bigClass where
  shape :=
    { requires := "Nothing of its own: the subject is a class of worlds with what the class states \
        and one agent, the subject of the postcondition's record, declared a plain value."
      rulesOut := "Nothing of its own."
      allows := "A class whose members' observations, rewards, dynamics or goals are constant, \
        which a shape that asks every function to vary with its input would not admit."
      freedom := "Two trials that meet the record may differ in everything the properties leave \
        open: the members and how many there are, which of them are counted, how long an attempt \
        lasts, and all the record does not read, which is the agent, how reward is aggregated, \
        the horizon and the lapses." }
  dom := []
  props := [
    { requires := "For every agent, every member and every attempt, some list of actions, fewer \
        than an attempt has steps, leads from the state the member's world is in when that \
        attempt of that agent's run starts to a state that meets the member's goal. The list may \
        be empty: a goal already met where the attempt starts counts as reached."
      rulesOut := "A class with a member whose goal no state meets, or whose goal lies as many \
        steps from where some attempt starts as an attempt has, or more."
      allows := "An action after which the goal can no longer be reached within the attempt: the \
        property asks nothing of the states an agent's own actions lead to."
      freedom := "Which actions reach each goal, and how many, below the attempt's length." },
    { requires := "There is one reference world, over the class's observations and actions, such \
        that for every agent, every member and every time up to and including which no state of \
        the agent's run in the member has met the member's goal, the member gives the agent at \
        that time the observation and the reward the reference world gives it at the same time \
        of its run there."
      rulesOut := "A class two of whose members give some agent different observations or \
        rewards at a time up to which neither's goal has been met in its run."
      allows := "Anything a member gives once its goal has been met in the run, the time it is \
        first met included; and a member whose goal is met where its run starts, of which the \
        property asks nothing."
      freedom := "The reference world, and what the members give after their goals are met." },
    { requires := "There is a number, smaller than the count of the counted members, such that \
        every agent that keeps nothing of its experience solves, on every attempt, at most that \
        many of the counted members."
      rulesOut := "A class in which some agent that keeps nothing of its experience solves every \
        counted member on some attempt, and a class that counts no member."
      allows := "Such an agent solving all the counted members but one; and any number of \
        members the class does not count, whoever solves them."
      freedom := "The bound, which members are counted, and what happens in the others." },
    { requires := "There is one function of an observation with a reward, the same for every \
        member, that returns, for every agent, every member and every time, from what the member \
        gives the agent at that time of its run, whether the state the member's world is then in \
        meets the member's goal."
      rulesOut := "A class in which a state that meets a member's goal and a state that does \
        not, of the same member or of two, give the same observation and reward; and a class in \
        which success shows only after the goal is met."
      allows := "Success shown by the observation, by the reward, or by both."
      freedom := "The function, and where in what the agent is given success shows." },
    { requires := "For every agent, every member and every attempt, the member's world is, when \
        that attempt of the agent's run in it starts, in the state the world starts in."
      rulesOut := "A class with a member that is not back in its start state after every \
        attempt's length of steps, whatever the agent does: a member with no restart, one whose \
        restart waits on an action of the agent, or one whose attempts end early."
      allows := "Anything between two starts."
      freedom := "What a member's world does within an attempt." }]
  vocab := [
    { requires := "The memory the agent's answer produces is the same whatever observation and \
        reward it was given."
      rulesOut := "An agent whose next memory depends on what it perceives."
      allows := "An agent whose action reads what it is given at that step, and one that counts \
        its steps."
      freedom := "None of its own: it is a definition the properties are written in." },
    { requires := "At the given time of the given agent's run in the given member, the member's \
        world is in a state that meets the member's goal."
      rulesOut := "A time at which the state does not meet the goal."
      allows := "Every time at which it does, the first of the run included."
      freedom := "None of its own: it is a definition the properties are written in." }]
  restatement := .confirmed owner
  consequences := [
    ⟨noFrozenAgentSolvesAll, noFrozenAgentSolvesAll_holds,
      { requires := "Every agent that keeps nothing of its experience solves, on every attempt, fewer of the counted members than the class counts."
        rulesOut := "A class in which some agent that keeps nothing of its experience solves every counted member on some attempt."
        allows := "Such an agent solving all the counted members but one."
        freedom := "How many fewer." }, .derived⟩,
    ⟨hasCountedMember, hasCountedMember_holds,
      { requires := "The class counts at least one member."
        rulesOut := "A class that counts no member."
        allows := "Nothing more."
        freedom := "Which members the class counts." }, .derived⟩,
    ⟨firstAttemptSmall, firstAttemptSmall_holds,
      { requires := "There is a number, smaller than the count of the counted members, such that every agent, one that learns included, solves at most that many of the counted members on its first attempt."
        rulesOut := "A class in which some agent solves every counted member on its first attempt."
        allows := "Any agent doing better on a later attempt."
        freedom := "The bound, and what agents do after their first attempt." }, .derived⟩,
    ⟨learningPays, learningPays_holds,
      { requires := "There is an agent that, on every attempt from the count of the counted members on, solves every counted member, and so solves on each of those attempts more counted members than any agent that keeps nothing of its experience solves on any attempt."
        rulesOut := "A class that meets the record and in which no agent ever solves more counted members than every agent that keeps nothing of its experience."
        allows := "An agent other than the class's own: the record reads no agent of the class."
        freedom := "Which agent; the one the proof names counts its steps and keeps the attempt on which what it was given first showed success." }, .derived⟩,
    ⟨rulesOutUnreachableGoals, rulesOutUnreachableGoals_holds,
      { requires := "The trial unreachable, the two-door class base with members whose goals no state meets, does not meet the record."
        rulesOut := "That trial; base meets the record (doors_big)."
        allows := "Nothing more."
        freedom := "Everything but being that one trial." }, .derived⟩,
    ⟨rulesOutShownGoals, rulesOutShownGoals_holds,
      { requires := "The trial revealing, base with members that show their door when they ask for one, does not meet the record."
        rulesOut := "That trial; base meets the record (doors_big)."
        allows := "Nothing more."
        freedom := "Everything but being that one trial." }, .derived⟩,
    ⟨rulesOutOneAnswer, rulesOutOneAnswer_holds,
      { requires := "The trial sameDoor, base with two members that have the same door, so that trying that door solves both, does not meet the record."
        rulesOut := "That trial; base meets the record (doors_big)."
        allows := "Nothing more."
        freedom := "Everything but being that one trial." }, .derived⟩,
    ⟨rulesOutHiddenSuccess, rulesOutHiddenSuccess_holds,
      { requires := "The trial hidden, base with members that pay nothing and show the same thing whether the door tried was right or wrong, does not meet the record."
        rulesOut := "That trial; base meets the record (doors_big)."
        allows := "Nothing more."
        freedom := "Everything but being that one trial." }, .derived⟩,
    ⟨rulesOutNoRecurrence, rulesOutNoRecurrence_holds,
      { requires := "The trial stuck, base with members that never ask for a door again after the first is tried, does not meet the record."
        rulesOut := "That trial; base meets the record (doors_big)."
        allows := "Nothing more."
        freedom := "Everything but being that one trial." }, .derived⟩,
    ⟨trapsAllowed, trapsAllowed_holds,
      { requires := "Nothing more: some trial that meets the record has a member and an action such that, from the state that action leads to from the member's start, no list of actions that fits in the rest of an attempt reaches a state that meets the member's goal, while a list no longer reaches one from the member's start."
        rulesOut := "Nothing."
        allows := "A trap within an attempt."
        freedom := "Whether a class has traps." }, .derived⟩]

end AcornVerif.Intent.BigClass
