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
  asked without condition (`AcornVerif.Intent.BigClass.retention_unconditional`).
* An agent that stores what it perceives and never reads it acts as some agent that keeps nothing
  acts, yet `KeepsNothing` does not hold of it. That such an agent fails the record in every class
  is not proved.

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
them, and the module of its consequences states the pair (`AcornVerif.Intent.BigClass.Served`) and
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

/-- **The promise about reward is a promise about members solved.** On some attempt the agent
solves more of the counted members than any agent that keeps nothing of its experience solves on any
attempt. -/
def solvesMoreEventually : Consequence Trial :=
  ⟨"on some attempt the agent solves more members than any agent that keeps nothing of its \
    experience solves on any attempt", .entailment, fun w =>
    ∃ n, ∀ B, KeepsNothing B → ∀ k, w.solvedCount B k < w.solvedCount w.agent n⟩

theorem solvesMoreEventually_holds : solvesMoreEventually.HoldsOf postcondition :=
  fun w hw =>
    let ⟨h1, ⟨n, hn⟩, _, _⟩ := postcondition_meets.mp hw
    ⟨n, fun B hB k => (h1 w.agent B (.inl rfl) (.inr hB) n k).mp (hn B hB k)⟩

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
  obtain ⟨n, hn⟩ := (postcondition_meets.mp hw).2.1
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

theorem forgetful_fails : ¬ postcondition.Meets forgetful := fun h =>
  absurd ((postcondition_meets.mp h).2.2.1 true 0 1 (by decide)
    (fun k _ _ => doors_sameProblem List.sum 1 once true 0 k) rfl) (by decide)

/-- **Solving a member once and never again is ruled out**, where the member's attempts start from
the same state: the trial `forgetful`. Its neighbour is `base`. -/
def rulesOutSolvingOnce : Consequence Trial :=
  ⟨"the trial forgetful, whose agent solves a member on its first attempt and never again, is \
    ruled out", .entailment, fun w => w ≠ forgetful⟩

theorem rulesOutSolvingOnce_holds : rulesOutSolvingOnce.HoldsOf postcondition :=
  fun _ hw he => forgetful_fails (he ▸ hw)

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

end AcornVerif.Intent.Postcondition
