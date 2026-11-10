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

Three things are not proved here, and each is a consequence for the owner's confirmation labelled
unproved, never a pass:

* A class whose members never start two attempts from the same state asks no retention: both
  `keepsSolving` and `learnsAgain` then hold of every agent. No trial is exhibited that meets the
  record while its agent solves a member once and never again, and none is refuted.
* An agent that stores what it perceives and never reads it acts as some agent that keeps nothing
  acts, yet `KeepsNothing` does not hold of it. That such an agent fails the record in every class
  is not proved.
* The trial-level check of lean-intent's degenerate subjects is not run: the subject's type holds
  types and functions, which that check does not cover. The trials attacked here are chosen by hand.

That the faithful run this record computes with, `Member.run`, is contract 1's faithful run never
stopped is stated in the record's module and is not proved against contract 1's `couple` here.
-/

namespace AcornVerif.Intent.Postcondition

open LeanIntent WorldInterface

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
