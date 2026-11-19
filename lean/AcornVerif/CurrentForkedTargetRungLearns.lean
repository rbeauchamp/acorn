/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentForkedTargetFrames
import AcornVerif.CurrentForkedTargetRungBoth
import AcornVerif.Targets.CurrentForkedTargetRung

/-!
# What follows from the target over the rung of targets by day and by night

`AcornVerif.Targets.CurrentForkedTargetRung.forks_learn` is the target of the discovery mission
that succeeds #283. This module proves what the statement excludes, what a proof of it gives, and
that its promises can be met. It proves nothing of the target itself.

**What mastery of a grid excludes**, at the rung's class and for every limit, horizon, lapses
and predicate:

- an agent that keeps nothing of its experience, at the sharp covering bound 49
  (`rung_grid_need`);
- an agent whose actions depend on its clock, its reward words and its achievement flags, at
  every bound (`rung_grid_blind`); such an agent serves at most one side of each fork
  (`AcornVerif.CurrentForkedTargetCandidate.rung_fork_sides`);
- an agent that differs from such an agent only on percepts the class never delivers
  (`rung_grid_hybrid`).

**What a proof of the target gives.**

- The executed agent masters a grid (`learns_masters`), so it is none of the excluded agents
  (`learns_not_blind`, `learns_not_free`).
- On some visit, from one memory at the visit's start, its actions differ between the visit's two
  situations (`learns_reads`).
- **It has met both situations.** Under every second target of the grid, some first target of
  the grid is one it had already solved, in that member's run, on an earlier visit of the first
  situation; and under every first target, some second target is one it had already solved on
  an earlier visit of the second situation (`learns_experienced`). The count behind it is
  sharper: under one second target, the first targets it solves on the visit of mastery without
  such an earlier visit number at most 49
  (`AcornVerif.CurrentForkedTargetBoth.grid_first_experience`).
- Each member of the grid is solved again, in each of its two runs, on every later visit before
  visit 1728 that brings the same situation, but for at most 288 visits (`learns_kept`). Visit
  576 leaves 1152 later visits, so the promise is not empty.

**What the target needs of the agent as it is.** Its literal conjuncts hold of the definitions
as they are, and the agent as it is meets the two clauses about how it acts, so the two promises
are all a proof for the unchanged agent has to supply (`learns_frame`).

**That the promises can be met.** `AcornVerif.CurrentForkedTargetRungBoth.gridWitness`, a kernel
agent built for the purpose, masters a grid of 56 first targets and 56 second targets at the
target's numbers under the predicate that admits every visit, and keeps on the visits of every
predicate (`witness_learns`). It records the actions of a rewarded visit for each situation it
reads and replays them, so it also shows that the two promises alone admit such an agent. It is
not an agent of the executed type, and the two clauses about how the executed agent acts are not
statements about it.

**That the clauses about acting leave room.** In every state of the rung's agent the frame laid
at the first situation's start holds a slot that the frame laid at the second's does not
(`AcornVerif.CurrentForkedTargetFrames.starts_differ`), so the frozen policy can value the two
situations differently.

Not proved here or anywhere: that one agent of the executed type meets the promises and the
clauses together, and whether the agent as it is meets either promise.
-/

namespace AcornVerif.CurrentForkedTargetRungLearns
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung
open AcornVerif.CurrentForkedTarget AcornVerif.CurrentForkedTargetRung
open AcornVerif.CurrentForkedTargetBoth AcornVerif.CurrentForkedTargetRungBoth
open AcornVerif.CurrentForkedTargetCalm AcornVerif.CurrentForkedTargetCandidate
open AcornVerif.Targets.CurrentForkedTargetRung

/-! ## What mastery of a grid excludes -/

/-- **No agent that keeps nothing masters a grid at the sharp covering bound**, whatever the
limit, the horizon, the lapses and the predicate. -/
theorem rung_grid_need (mode : TaskFeatureMode) {agent : Kernel.Agent Grid.interface}
    (free : Kernel.ExperienceFree agent) (limit horizon lapses : ℕ)
    (admits : (rungForks mode).Index → (ℕ → Bool) → ℕ → Prop) :
    ¬ Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 49
      (firstTarget mode witnessLive duskLive 7) (secondTarget mode witnessLive duskLive 7)
      limit horizon lapses admits agent :=
  forked_need_grid mode witnessLive duskLive 7 free limit horizon lapses admits

/-- **No agent that goes by its clock, its reward words and its achievement flags masters a
grid**, at any bound, keys, limit, horizon, lapses and predicate. -/
theorem rung_grid_blind (mode : TaskFeatureMode) {agent : Kernel.Agent Grid.interface}
    (blind : Kernel.FeedbackDriven rewardAndFlag agent) (bound limit horizon lapses : ℕ)
    {κ μ : Type} (one : (rungForks mode).Index → κ) (two : (rungForks mode).Index → μ)
    (admits : (rungForks mode).Index → (ℕ → Bool) → ℕ → Prop) :
    ¬ Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 bound one two limit horizon
      lapses admits agent :=
  forked_blind_grid mode witnessLive duskLive 7 dusk_carried blind bound limit horizon lapses
    one two admits

/-- **An agent that differs from such an agent only where the class never looks masters no
grid.** -/
theorem rung_grid_hybrid (mode : TaskFeatureMode) {E Core V : Type}
    (select : E → V → Kernel.Act Grid.interface × E) (core : Core) (seed : E)
    (prefer : Core → Binary32 × Bool → V)
    (advance : Core → Binary32 × Bool → Kernel.Act Grid.interface → Core)
    (alien : Percept Grid.interface → Prop) [DecidablePred alien] (rest : V)
    (never : ∀ state : Option (Live witnessConfig),
      ¬ alien ((gridWorld witnessConfig mode).percept state))
    (bound limit horizon lapses : ℕ) {κ μ : Type} (one : (rungForks mode).Index → κ)
    (two : (rungForks mode).Index → μ)
    (admits : (rungForks mode).Index → (ℕ → Bool) → ℕ → Prop) :
    ¬ Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 bound one two limit horizon
      lapses admits
      (Kernel.chooser select core seed
        (Kernel.aloof alien rest (fun inner percept => prefer inner (rewardAndFlag percept)))
        (fun inner percept action => advance inner (rewardAndFlag percept) action)) :=
  Kernel.aloof_mastersGrid select core seed prefer advance alien rest
    (fun _ state => never state) (forked_mute mode witnessLive duskLive 7 dusk_carried)
    (forked_apart mode witnessLive duskLive 7)

/-! ## What a proof of the target gives -/

/-- **The target follows from its two promises.** Its literal conjuncts hold of the definitions
as they are, and the agent as it is meets the two clauses about how it acts. So for the unchanged
agent, the two promises under one planning selection are a proof of the target. It proves neither
promise. -/
theorem learns_frame (planning : PlanningSelection)
    (masters : Kernel.MastersGridBy (rungForks (rungConstruction planning).profile.taskMode)
      (rungForkGoals (rungConstruction planning).profile.taskMode) 7 49
      (firstTarget (rungConstruction planning).profile.taskMode witnessLive duskLive 7)
      (secondTarget (rungConstruction planning).profile.taskMode witnessLive duskLive 7)
      576 1728 288 (TurnCalm planning)
      (executedAgent (rungConstruction planning).initial.agent))
    (keeps : Kernel.KeepsOn (rungForks (rungConstruction planning).profile.taskMode)
      (rungForkGoals (rungConstruction planning).profile.taskMode) 7 1728
      (TurnCalm planning) (executedAgent (rungConstruction planning).initial.agent)) :
    forks_learn :=
  ⟨rfl, rfl, rfl, rfl, rfl, planning, rfl, rfl, rfl, rfl, rfl, masters, keeps,
    acts_met planning, starts_cold_met planning⟩

/-- From a proof of the target, the executed agent masters a grid before visit 576, for its
planning selection. -/
theorem learns_masters (learns : forks_learn) :
    ∃ planning : PlanningSelection,
      Kernel.MastersGridBy (rungForks (rungConstruction planning).profile.taskMode)
        (rungForkGoals (rungConstruction planning).profile.taskMode) 7 49
        (firstTarget (rungConstruction planning).profile.taskMode witnessLive duskLive 7)
        (secondTarget (rungConstruction planning).profile.taskMode witnessLive duskLive 7)
        576 1728 288 (TurnCalm planning)
        (executedAgent (rungConstruction planning).initial.agent) := by
  obtain ⟨-, -, -, -, -, planning, -, -, -, -, -, masters, -, -, -⟩ := learns
  exact ⟨planning, masters⟩

/-- **An agent that meets the target is not driven by its reward words and achievement flags.** -/
theorem learns_not_blind (learns : forks_learn) :
    ∃ planning : PlanningSelection, ¬ Kernel.FeedbackDriven rewardAndFlag
      (executedAgent (rungConstruction planning).initial.agent) := by
  obtain ⟨planning, masters⟩ := learns_masters learns
  exact ⟨planning, fun blind => rung_grid_blind _ blind 49 576 1728 288 _ _ _ masters⟩

/-- **An agent that meets the target keeps something of its experience.** -/
theorem learns_not_free (learns : forks_learn) :
    ∃ planning : PlanningSelection, ¬ Kernel.ExperienceFree
      (executedAgent (rungConstruction planning).initial.agent) := by
  obtain ⟨planning, masters⟩ := learns_masters learns
  exact ⟨planning, fun free => rung_grid_need _ free 576 1728 288 _ masters⟩

/-- **An agent that meets the target reads what it perceives.** From a proof of the target: for
its planning selection there are an order, a visit, a member and a step of that visit at which
the executed agent's actions differ between the two runs that differ in that visit's situation
alone, while its memory at the visit's start is the same in both. -/
theorem learns_reads (learns : forks_learn) :
    ∃ (planning : PlanningSelection) (order : ℕ → Bool) (visit : ℕ)
      (pair : (rungForks (rungConstruction planning).profile.taskMode).Index) (step : ℕ),
      step < 7 ∧
        Kernel.turnMemory ((rungForks (rungConstruction planning).profile.taskMode).world pair)
            ((rungForks (rungConstruction planning).profile.taskMode).start pair)
            (Function.update order visit false) 7
            (executedAgent (rungConstruction planning).initial.agent) visit =
          Kernel.turnMemory ((rungForks (rungConstruction planning).profile.taskMode).world pair)
            ((rungForks (rungConstruction planning).profile.taskMode).start pair)
            (Function.update order visit true) 7
            (executedAgent (rungConstruction planning).initial.agent) visit ∧
        Kernel.actionAt
            (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair)
              (Function.update order visit false) 7)
            (executedAgent (rungConstruction planning).initial.agent)
            (Kernel.turnStart
              ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair)
              (Function.update order visit false) 7 0) (visit * (7 + 1) + step) ≠
          Kernel.actionAt
            (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair)
              (Function.update order visit true) 7)
            (executedAgent (rungConstruction planning).initial.agent)
            (Kernel.turnStart
              ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair)
              (Function.update order visit true) 7 0) (visit * (7 + 1) + step) := by
  obtain ⟨planning, masters⟩ := learns_masters learns
  obtain ⟨order, visit, pair, -, solved⟩ := masters.solves
  obtain ⟨step, short, differ⟩ := Kernel.turn_differs
    (forked_apart (rungConstruction planning).profile.taskMode witnessLive duskLive 7) order
    (executedAgent (rungConstruction planning).initial.agent) visit pair solved
  exact ⟨planning, order, visit, pair, step, short,
    (Kernel.turnMemory_sides _ _ order 7 _ visit false).trans
      (Kernel.turnMemory_sides _ _ order 7 _ visit true).symm, differ⟩

/-- **An agent that meets the target has met both situations.** From a proof of the target: for
its planning selection there are an order, a visit and a grid of more than 49 first targets and
more than 49 second targets such that, under every second target of the grid, some first target
of the grid is one the agent had already solved, in that member's run, on an earlier visit of the
first situation; and under every first target, some second target is one it had already solved
on an earlier visit of the second situation. What it met in one situation did not supply the
other's answer. -/
theorem learns_experienced (learns : forks_learn) :
    ∃ (planning : PlanningSelection) (order : ℕ → Bool) (visit : ℕ)
      (firsts : Finset (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        witnessLive 7).Index)
      (seconds : Finset (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        duskLive 7).Index),
      49 < firsts.card ∧ 49 < seconds.card ∧
      (∀ two ∈ seconds, ∃ pair : (rungForks (rungConstruction planning).profile.taskMode).Index,
        secondTarget (rungConstruction planning).profile.taskMode
          witnessLive duskLive 7 pair = two ∧
          firstTarget (rungConstruction planning).profile.taskMode
            witnessLive duskLive 7 pair ∈ firsts ∧
          ∃ earlier, earlier < visit ∧ order earlier = false ∧
            Kernel.SolvesTurn (rungForks (rungConstruction planning).profile.taskMode)
              (rungForkGoals (rungConstruction planning).profile.taskMode) 7 order
              (executedAgent (rungConstruction planning).initial.agent) earlier pair) ∧
      (∀ one ∈ firsts, ∃ pair : (rungForks (rungConstruction planning).profile.taskMode).Index,
        firstTarget (rungConstruction planning).profile.taskMode witnessLive duskLive 7 pair = one ∧
          secondTarget (rungConstruction planning).profile.taskMode
            witnessLive duskLive 7 pair ∈ seconds ∧
          ∃ earlier, earlier < visit ∧ order earlier = true ∧
            Kernel.SolvesTurn (rungForks (rungConstruction planning).profile.taskMode)
              (rungForkGoals (rungConstruction planning).profile.taskMode) 7 order
              (executedAgent (rungConstruction planning).initial.agent) earlier pair) := by
  obtain ⟨planning, order, visit, firsts, seconds, -, manyFirst, manySecond, each⟩ :=
    learns_masters learns
  refine ⟨planning, order, visit, firsts, seconds, manyFirst, manySecond,
    fun two inSeconds => ?_, fun one inFirsts => ?_⟩
  · by_contra none
    have few := grid_first_experience (rungConstruction planning).profile.taskMode witnessLive
      duskLive 7 (executedAgent (rungConstruction planning).initial.agent) order visit firsts two
      (fun own inFirsts => by
        obtain ⟨pair, isOne, isTwo, solved⟩ := each own inFirsts two inSeconds
        exact ⟨pair, isOne, isTwo, (solved false).1, fun earlier early side found =>
          none ⟨pair, isTwo, by rw [isOne]; exact inFirsts, earlier, early, side, found⟩⟩)
    omega
  · by_contra none
    have few := grid_second_experience (rungConstruction planning).profile.taskMode witnessLive
      duskLive 7 (executedAgent (rungConstruction planning).initial.agent) order visit seconds one
      (fun own inSeconds => by
        obtain ⟨pair, isOne, isTwo, solved⟩ := each one inFirsts own inSeconds
        exact ⟨pair, isTwo, isOne, (solved true).1, fun earlier early side found =>
          none ⟨pair, isOne, by rw [isTwo]; exact inSeconds, earlier, early, side, found⟩⟩)
    omega

/-- **An agent that meets the target keeps the grid.** From a proof of the target: for its
planning selection there are an order, a visit before visit 576 and a grid of more than 49 first
targets and more than 49 second targets, each member of which the executed agent solves again,
in each of the two runs of that visit, on every later visit before visit 1728 that brings that
run's situation of that visit, but for at most 288 visits. -/
theorem learns_kept (learns : forks_learn) :
    ∃ (planning : PlanningSelection) (order : ℕ → Bool) (visit : ℕ)
      (firsts : Finset (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        witnessLive 7).Index)
      (seconds : Finset (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        duskLive 7).Index),
      visit < 576 ∧ 49 < firsts.card ∧ 49 < seconds.card ∧
      ∀ one ∈ firsts, ∀ two ∈ seconds,
        ∃ pair : (rungForks (rungConstruction planning).profile.taskMode).Index,
          firstTarget (rungConstruction planning).profile.taskMode
            witnessLive duskLive 7 pair = one ∧
          secondTarget (rungConstruction planning).profile.taskMode
            witnessLive duskLive 7 pair = two ∧
          ∀ situation : Bool, ∃ lapsed : Finset ℕ, lapsed.card ≤ 288 ∧
            ∀ later, visit < later → later < 1728 →
              Function.update order visit situation later = situation → later ∉ lapsed →
                Kernel.SolvesTurn (rungForks (rungConstruction planning).profile.taskMode)
                  (rungForkGoals (rungConstruction planning).profile.taskMode) 7
                  (Function.update order visit situation)
                  (executedAgent (rungConstruction planning).initial.agent) later pair := by
  obtain ⟨-, -, -, -, -, planning, -, -, -, -, -, masters, keeps, -, -⟩ := learns
  obtain ⟨order, visit, firsts, seconds, rest⟩ := masters.kept keeps
  exact ⟨planning, order, visit, firsts, seconds, rest⟩

/-! ## That the promises can be met -/

/-- **The witness meets both promises at the target's numbers.** For every task mode, the agent
`AcornVerif.CurrentForkedTargetRungBoth.gridWitness` masters a grid before visit 576, at the
horizon 1728 and 288 lapses, under the predicate that admits every visit, and keeps before visit
1728 on the visits of every predicate. It is a kernel agent built for the purpose, which records
a rewarded visit's actions for each situation and replays them. -/
theorem witness_learns (mode : TaskFeatureMode) :
    Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 49
        (firstTarget mode witnessLive duskLive 7) (secondTarget mode witnessLive duskLive 7)
        576 1728 288 (fun _ _ _ => True) gridWitness ∧
      ∀ admits, Kernel.KeepsOn (rungForks mode) (rungForkGoals mode) 7 1728 admits
        gridWitness :=
  ⟨(grid_witness_masters mode 1728 288).mono (by decide),
    fun admits => (grid_witness_keeps mode 1728).on admits⟩

end AcornVerif.CurrentForkedTargetRungLearns
