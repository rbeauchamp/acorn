/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.Intent.Postcondition

/-!
# The consequences of the record of the postcondition

Each consequence of `AcornVerif.Intent.Postcondition.postcondition` stated here is proved to hold of
the record: what it requires of every trial that meets it, the trials it rules out, each beside
`base`, the trial that differs from it only where it attacks and meets the record, and what the
record still allows.

Two things are not proved here, and each is a consequence for the owner's confirmation labelled
unproved, never a pass:

* A class whose members never start two attempts from the same state asks no retention: both
  `keepsSolving` and `learnsAgain` then hold of every agent. No trial is exhibited that meets the
  record while its agent solves a member once and never again, and none is refuted. In a class that
  meets the record of contract 2 every attempt starts from the same state, so there retention is
  asked with no condition on the member's attempts
  (`AcornVerif.Intent.BigClass.retention_unconditional`).
* An agent that stores what it perceives and never reads it acts as some agent that keeps nothing
  acts, yet `KeepsNothing` does not hold of it. That such an agent fails the record in every class
  is not proved.

The record ties the two numbers a class names, its horizon and its lapses, through the attempt of
the advantage, which leaves more later attempts before the horizon than the lapses. So each
member the agent solves on that attempt it solves again on a later one, where that member's
later attempts start from the same state (`advantageSolvedAgain`), as they do in every class
that meets the record of contract 2 (`AcornVerif.Intent.BigClass.advantage_solved_again`). A
two-door agent that earns its advantage once and solves nothing afterwards fails the record
(`rulesOutAdvantageOnce`), and so does the class whose horizon comes right after the attempt of
its agent's advantage (`rulesOutLateAdvantage`). A class that allows as many lapses as it has
attempts before its horizon, less one, asks no retention, since `keepsSolving` and `learnsAgain`
then hold of every agent (`keepsSolving_of_lapses`, `learnsAgain_of_lapses`); no agent meets the
record in such a class, because no attempt leaves that room (`unmet_of_lapses`). What the record
still allows is anything from the horizon on, and a member first solved on the last attempt
before the horizon and never again.

Two checks of lean-intent were not run:

* Its degenerate-subject and trivial-witness checks cover a subject in `Type`, and `Trial` carries
  its own types, so it lives one universe higher (rbeauchamp/lean-intent#43). The interim class for
  a plain value asks for its empty value and `default`, and `Trial` has neither. The nearest
  subjects are attacked by hand and both fail the record: a class that counts no member
  (`countsSomeMember_holds`, `uncounted_fails`), and an agent that keeps nothing of its experience,
  which a script of timed actions is, in every class (`not_earnsMore_of_keepsNothing`,
  `learnerKeepsSomething_holds`).
* Its cone exclusion: no implementation of this record is named yet, and the record's module
  imports contract 1's record and lean-intent only, so none of the modules that define the kernel's
  worlds, classes and visits, or the executing agent, is in its imports.

The pair whose input is the class of worlds is not discharged here. With no domain hypothesis the
record admits classes that no agent can serve, as `uncounted_fails` shows, so that pair needs the
preconditions of contract 2. The record of contract 2, `AcornVerif.Intent.BigClass.bigClass`, states
those of them it carries, conditions (a) to (c) and sentence 6, and not condition (d); the module of
its consequences states the pair (`AcornVerif.Intent.BigClass.Served`) and
leaves it unproved for every class but the two-door ones. What is proved here is the pair with the
trivial input (`postcondition_pairs`) and that one agent, `finder`, serves every two-door class
with a fair aggregation and payment (`doors_finder_meets`).
-/

namespace AcornVerif.Intent.Postcondition

open LeanIntent WorldInterface

/-! ## The run is contract 1's -/

/-- The member `M` as a world of contract 1, with every action available at every state. -/
def Member.world {Obs Act : Type} (M : Member Obs Act) : World where
  State := M.State
  Obs := Obs
  Act := Act
  start := M.start
  observe := M.observe
  reward := M.reward
  available := fun _ _ => True
  step := M.step

/-- **The run the record computes with is contract 1's faithful run, never stopped.** After any
number of steps, the faithful run of contract 1 of a member's world and an agent, sent no stop
request, has reached the state and the memory that `Member.run` gives. -/
theorem run_reaches {Obs Act : Type} (M : Member Obs Act) (A : Agent Obs Act) :
    ∀ t, (couple M.world A).Reaches neverStop t (M.run A t).1 (M.run A t).2
  | 0 => .start
  | t + 1 => .next (run_reaches M A t) rfl

/-! ## What the record requires -/

/-- **The agent keeps something of its experience.** -/
def learnerKeepsSomething : Consequence Trial :=
  ⟨"the agent keeps something of its experience", .entailment, fun w => ¬ KeepsNothing w.agent⟩

theorem learnerKeepsSomething_holds : learnerKeepsSomething.HoldsOf postcondition :=
  fun _ hw hk => not_earnsMore_of_keepsNothing hk (postcondition_meets.mp hw).2.1

/-- **The promise about reward is a promise about members solved.** On some attempt that leaves
more later attempts before the horizon than the lapses, the agent solves more of the counted
members than any agent that keeps nothing of its experience solves on any attempt. -/
def solvesMoreInTime : Consequence Trial :=
  ⟨"on some attempt that leaves more later attempts before the stated attempt than the stated \
    number of lapses, the agent solves more members than any agent that keeps nothing of its \
    experience solves on any attempt", .entailment, fun w =>
    ∃ n, n + w.lapses + 1 < w.horizon ∧
      ∀ B, KeepsNothing B → ∀ k, w.solvedCount B k < w.solvedCount w.agent n⟩

theorem solvesMoreInTime_holds : solvesMoreInTime.HoldsOf postcondition :=
  fun w hw =>
    let ⟨h1, ⟨n, room, hn⟩, _, _⟩ := postcondition_meets.mp hw
    ⟨n, room, fun B hB k => (h1 w.agent B (.inl rfl) (.inr hB) n k).mp (hn B hB k)⟩

/-- **The members solved on the attempt of the advantage are solved again.** On some attempt the
agent earns more across the class than any agent that keeps nothing of its experience earns on
any attempt, and each member it solves on that attempt it solves again on a later attempt before
the horizon, where that member's later attempts start from the state that attempt started from. -/
def advantageSolvedAgain : Consequence Trial :=
  ⟨"each member the agent solves on the attempt of its advantage it solves again on a later \
    attempt before the stated attempt, where the member's later attempts start from the same \
    state", .entailment, fun w =>
    ∃ n, (∀ B, KeepsNothing B → ∀ k, w.classReward B k < w.classReward w.agent n) ∧
      ∀ i, w.solves w.agent i n = true → (∀ k, n < k → w.SameProblem i n k) →
        ∃ n', n < n' ∧ n' < w.horizon ∧ w.solves w.agent i n' = true⟩

theorem advantageSolvedAgain_holds : advantageSolvedAgain.HoldsOf postcondition :=
  fun w hw =>
    let ⟨_, ⟨n, room, more⟩, _, again⟩ := postcondition_meets.mp hw
    ⟨n, more, fun i solved same =>
      let ⟨n', low, high, hs⟩ := again i n (n + 1) (Nat.le_succ n) (by omega)
        (fun k later => same k later) solved
      ⟨n', low, by omega, hs⟩⟩

/-- The agent that answers each thing it is given as `A` answers it from its initial memory, and
keeps nothing of its experience. -/
def shell {Obs Act : Type} (A : Agent Obs Act) : Agent Obs Act where
  Memory := Unit
  initial := ()
  act := fun _ o => ((A.act A.initial o).1, ())

theorem shell_keepsNothing {Obs Act : Type} (A : Agent Obs Act) : KeepsNothing (shell A) :=
  fun _ _ _ => rfl

/-- **The class counts at least one member.** With no member counted, every agent earns nothing
across the class on every attempt, so the agent earns no more than an agent that keeps nothing. -/
def countsSomeMember : Consequence Trial :=
  ⟨"the class counts at least one member", .entailment, fun w => w.counted ≠ []⟩

theorem countsSomeMember_holds : countsSomeMember.HoldsOf postcondition := by
  intro w hw he
  obtain ⟨n, -, hn⟩ := (postcondition_meets.mp hw).2.1
  have h := hn (shell w.agent) (shell_keepsNothing _) n
  unfold Trial.classReward at h
  rw [he] at h
  exact Rat.lt_irrefl h

/-! ## What the record rules out -/

theorem fixed_fails : ¬ postcondition.Meets fixed := fun h =>
  not_earnsMore_of_keepsNothing (w := fixed) (always_keepsNothing true)
    (postcondition_meets.mp h).2.1

/-- **An agent that always acts the same is ruled out**: the trial `fixed`, whose agent tries the
first door on every attempt. Its neighbour is `base`. -/
def rulesOutFixedAgent : Consequence Trial :=
  ⟨"the trial fixed, whose agent tries the same door on every attempt, is ruled out", .entailment,
    fun w => w ≠ fixed⟩

theorem rulesOutFixedAgent_holds : rulesOutFixedAgent.HoldsOf postcondition :=
  fun _ hw he => fixed_fails (he ▸ hw)

theorem unpaid_fails : ¬ postcondition.Meets unpaid := fun h => by
  have hlt : unpaid.classReward (always true) 0 < unpaid.classReward finder 1 :=
    ((postcondition_meets.mp h).1 finder (always true) (.inl rfl)
      (.inr (always_keepsNothing true)) 1 0).mpr (by decide)
  exact absurd hlt (by decide +kernel)

/-- **A class whose reward does not show its goals is ruled out**: the trial `unpaid`, whose members
pay nothing when their door is tried. Its neighbour is `base`. -/
def rulesOutUnpaidGoals : Consequence Trial :=
  ⟨"the trial unpaid, whose members generate no reward at their goals, is ruled out", .entailment,
    fun w => w ≠ unpaid⟩

theorem rulesOutUnpaidGoals_holds : rulesOutUnpaidGoals.HoldsOf postcondition :=
  fun _ hw he => unpaid_fails (he ▸ hw)

theorem forgetful_fails : ¬ postcondition.Meets forgetful := fun h => by
  obtain ⟨lapsed, few, keeps⟩ := (postcondition_meets.mp h).2.2.1 true
  have none : lapsed = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp few)
  exact absurd (keeps 0 1 (by decide) (by decide)
    (fun k _ _ => doors_sameProblem List.sum 1 once true 0 k) rfl
    (by rw [none]; exact List.not_mem_nil)) (by decide)

/-- **Solving a member once and never again is ruled out**, where the member's attempts start from
the same state, a later attempt comes before the class's horizon and the class allows no lapse:
the trial `forgetful`. Its neighbour is `base`. -/
def rulesOutSolvingOnce : Consequence Trial :=
  ⟨"the trial forgetful, whose agent solves a member on its first attempt and never again, is \
    ruled out", .entailment, fun w => w ≠ forgetful⟩

theorem rulesOutSolvingOnce_holds : rulesOutSolvingOnce.HoldsOf postcondition :=
  fun _ hw he => forgetful_fails (he ▸ hw)

/-- An agent that tries the first door on its first attempt, the member's door on its second
attempt, and the other door ever after. Its memory counts its steps and keeps the door the first
attempt showed. -/
def flash : Agent (Option Bool) Bool where
  Memory := Nat × Option Bool
  initial := (0, none)
  act := fun m o =>
    (if m.1 == 0 then true else if m.1 == 2 then m.2.getD true else !(m.2.getD true),
      (m.1 + 1, if m.1 == 1 then o.1 else m.2))

/-- From its second attempt on, `flash` has counted its steps and holds the member's door. -/
theorem flash_memory (pay : Rat) (b : Bool) :
    ∀ t, ((door pay b).run flash (t + 2)).2 = (t + 2, some b)
  | 0 => by cases b <;> rfl
  | t + 1 => by
    have ih := flash_memory pay b t
    show (flash.act ((door pay b).run flash (t + 2)).2 _).2 = _
    rw [ih]
    rfl

/-- On its second attempt `flash` solves each member of a two-door class. -/
theorem flash_hits (total : List Rat → Rat) (pay : Rat) (X : Agent (Option Bool) Bool)
    (b : Bool) : (doors total pay X).solves flash b 1 = true := by
  rw [doors_solves]
  cases b <;> rfl

/-- From its third attempt on `flash` solves no member of a two-door class. -/
theorem flash_misses (total : List Rat → Rat) (pay : Rat) (X : Agent (Option Bool) Bool)
    (b : Bool) (n : Nat) : (doors total pay X).solves flash b (n + 2) = false := by
  have h : tried pay flash b (n + 2) = !b := by
    unfold tried
    have e : 2 * (n + 2) = 2 * n + 2 + 2 := by omega
    rw [e, flash_memory]
    rfl
  rw [doors_solves, h]
  cases b <;> rfl

/-- `base` whose agent is `flash`: it earns the advantage on its second attempt and solves no
member afterwards. -/
def flashy : Trial := doors List.sum 1 flash

/-- `flashy` meets the record's property on the advantage: on its second attempt its agent earns
more than any agent that keeps nothing of its experience, with a later attempt left before the
horizon. -/
theorem flashy_earnsMore : earnsMoreInTime.holds flashy := by
  refine ⟨1, show 1 + 0 + 1 < 3 by decide, fun (B : Agent (Option Bool) Bool) hB k => ?_⟩
  show (doors List.sum 1 flash).classReward B k < (doors List.sum 1 flash).classReward flash 1
  rw [doors_classReward, doors_classReward, flash_hits, flash_hits, doors_solves, doors_solves,
    keepsNothing_tried 1 hB, keepsNothing_tried 1 hB]
  exact (fair_sum_one _ _ _ _).mpr (by cases guess B k <;> decide)

/-- `flashy` fails the record: it solves the first member on its second attempt and not on its
third, which comes before the horizon, and the class allows no lapse. -/
theorem flashy_fails : ¬ postcondition.Meets flashy := fun h => by
  obtain ⟨lapsed, few, keeps⟩ := (postcondition_meets.mp h).2.2.1 true
  have none : lapsed = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp few)
  have again := keeps 1 2 (by decide) (by decide)
    (fun k _ _ => doors_sameProblem List.sum 1 flash true 1 k) (flash_hits List.sum 1 flash true)
    (by rw [none]; exact List.not_mem_nil)
  exact Bool.noConfusion (again.symm.trans (flash_misses List.sum 1 flash true 0))

/-- **An advantage earned once and never repeated is ruled out**: the trial `flashy`, whose agent
earns more than every agent that keeps nothing on its second attempt and solves no member from
its third attempt on. It meets the record's first two properties (`doors_rewardCounts`,
`flashy_earnsMore`) and fails by `keepsSolving`. Its neighbour is `base`. -/
def rulesOutAdvantageOnce : Consequence Trial :=
  ⟨"the trial flashy, whose agent earns the advantage on its second attempt and solves no member \
    afterwards, is ruled out", .entailment, fun w => w ≠ flashy⟩

theorem rulesOutAdvantageOnce_holds : rulesOutAdvantageOnce.HoldsOf postcondition :=
  fun _ hw he => flashy_fails (he ▸ hw)

/-- `base` with no member counted. -/
def uncounted : Trial := { base with counted := [] }

theorem uncounted_fails : ¬ postcondition.Meets uncounted := fun h =>
  countsSomeMember_holds _ h rfl

/-! ## What the record still allows -/

/-- **No advantage on a first attempt**: some trial that meets the record has an agent that, on its
first attempt, earns no more across the class than an agent that keeps nothing of its experience. -/
def noFirstAttemptAdvantage : Consequence Trial :=
  ⟨"on its first attempt the agent may earn no more than an agent that keeps nothing of its \
    experience", .possibility, fun w =>
    ∃ B, KeepsNothing B ∧ ¬ w.classReward B 0 < w.classReward w.agent 0⟩

theorem noFirstAttemptAdvantage_holds : noFirstAttemptAdvantage.HoldsOf postcondition :=
  ⟨base, base_meets, always true, always_keepsNothing true, by decide +kernel⟩

/-- **A member may go unsolved on a first attempt**: some trial that meets the record has an agent
that does not solve one of the counted members on its first attempt. -/
def firstAttemptMayFail : Consequence Trial :=
  ⟨"the agent may fail to solve a member on its first attempt", .possibility, fun w =>
    ∃ i, i ∈ w.counted ∧ w.solves w.agent i 0 = false⟩

theorem firstAttemptMayFail_holds : firstAttemptMayFail.HoldsOf postcondition :=
  ⟨base, base_meets, false, .tail _ (.head _), rfl⟩

/-- **A class whose lapses cover its later attempts asks no solving again.** Where a class allows
as many lapses as it has attempts before its horizon, less one, `keepsSolving` holds of every
agent: every attempt before the horizon but the first may be a lapse, and the first attempt is
later than none. -/
theorem keepsSolving_of_lapses (w : Trial) (covered : w.horizon ≤ w.lapses + 1) :
    keepsSolving.holds w :=
  fun _ => ⟨List.range' 1 (w.horizon - 1), by rw [List.length_range']; omega,
    fun n n' hle before _ hs out => by
      have zero : n' = 0 := by
        rcases Nat.eq_zero_or_pos n' with h | h
        · exact h
        · exact absurd (List.mem_range'_1.mpr ⟨h, by omega⟩) out
      subst zero
      have first : n = 0 := Nat.le_zero.mp hle
      subst first
      exact hs⟩

/-- Where a class allows as many lapses as it has attempts before its horizon, less one,
`learnsAgain` holds of every agent: only the first attempt leaves more attempts than the lapses
before the horizon, and the attempt solved no later than the first is the first. -/
theorem learnsAgain_of_lapses (w : Trial) (covered : w.horizon ≤ w.lapses + 1) :
    learnsAgain.holds w :=
  fun _ n n' hle room _ hs => by
    have zero : n' = 0 := by omega
    subst zero
    have first : n = 0 := Nat.le_zero.mp hle
    subst first
    exact ⟨0, Nat.le_refl 0, Nat.zero_le _, hs⟩

/-- `base` with its promises read over its first two attempts only. -/
def hurried : Trial := { base with horizon := 2 }

/-- `hurried` fails the record: only its first attempt leaves a later attempt before the horizon,
and on that attempt `finder` earns no more than the agent that always tries the first door. -/
theorem hurried_fails : ¬ postcondition.Meets hurried := fun h => by
  obtain ⟨n, room, more⟩ := (postcondition_meets.mp h).2.1
  have small : n + 0 + 1 < 2 := room
  have first : n = 0 := by omega
  subst first
  exact absurd (more (always true) (always_keepsNothing true) 0) (by decide +kernel)

/-- **An advantage that comes too late for the horizon is ruled out**: the trial `hurried`, whose
agent earns the advantage on its second attempt, the last before the class's horizon. Its
neighbour is `base`, which reads one attempt more. -/
def rulesOutLateAdvantage : Consequence Trial :=
  ⟨"the trial hurried, whose agent earns the advantage on the last attempt before the stated \
    attempt, is ruled out", .entailment, fun w => w ≠ hurried⟩

theorem rulesOutLateAdvantage_holds : rulesOutLateAdvantage.HoldsOf postcondition :=
  fun _ hw he => hurried_fails (he ▸ hw)

/-- **No agent meets the record in a class whose lapses leave no room.** Where a class allows as
many lapses as it has attempts before its horizon, less one, no attempt leaves more later
attempts before the horizon than the lapses, so the record's property on the advantage fails of
every agent. -/
theorem unmet_of_lapses (w : Trial) (covered : w.horizon ≤ w.lapses + 1) :
    ¬ postcondition.Meets w := fun h => by
  obtain ⟨n, room, -⟩ := (postcondition_meets.mp h).2.1
  omega

end AcornVerif.Intent.Postcondition
