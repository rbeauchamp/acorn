/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentForkedTargetFrames
import AcornVerif.CurrentForkedTargetRule
import AcornVerif.CurrentForkedTargetRungBoth

/-!
# What mastery of a grid of targets by day and by night excludes and gives

This module is about the promises a statement over the rung of targets by day and by night can
be built from: mastery of a grid (`AcornVerif.Kernel.MastersGridBy`), keeping on admitted
visits (`AcornVerif.Kernel.KeepsOn`), and the two clauses of
`AcornVerif.CurrentForkedTargetRule`. It proves what they exclude, what follows from them, and
that the two promises can be met. It states no target and proves none.

**What mastery of a grid excludes**, at the rung's class and for every limit, horizon, returns
and predicate:

- an agent that keeps nothing of its experience, at the sharp covering bound 49
  (`rung_grid_need`);
- an agent whose actions depend on its clock, its reward words and its achievement flags, at
  every bound (`rung_grid_blind`);
- the kernel's chooser over that feedback, made to act otherwise only on percepts the class
  never delivers (`rung_grid_hybrid`).

**What mastery of a grid gives**, for every agent of the grid interface:

- on some visit, from one memory at the visit's start, the agent's actions differ at some step
  between the visit's two situations (`grid_reads`); the theorem gives one step, not the first;
- under every second target of the grid, some first target is one the agent had already solved,
  in that member's run, on an earlier visit of the first situation, and under every first
  target some second target is one it had already solved on an earlier visit of the second
  situation (`grid_experienced`). The count behind it: under one second target, the first
  targets solved on the visit of mastery without such an earlier visit number at most 49
  (`AcornVerif.CurrentForkedTargetBoth.grid_first_experience`).

**What the rule adds**, for the executed agent of a construction that steps by the declared
rule: on a calm visit of a member's run, each of the seven actions the world takes is the greedy
choice among the values the primitive controller holds at that decision's frame
(`calm_turn_greedy`). With mastery on a calm visit, the visit of mastery is solved by such
choices.

**That the two promises can be met.** `AcornVerif.CurrentForkedTargetRungBoth.gridWitness`, a
kernel agent built for the purpose, masters a grid before visit 576 with 288 later occasions
before visit 1728, under the predicate that admits every visit, and keeps on the visits of every
predicate (`witness_promises`). It records the actions of a rewarded visit for each situation it
reads and replays them. It is not an agent of the executed type: it has no draw, so it shows
nothing about calm visits, and it does not step by the declared rule.

**That the rule leaves the values room.** In every state of the rung's agent the frame laid at
the first situation's start holds a slot that the frame laid at the second's does not
(`AcornVerif.CurrentForkedTargetFrames.starts_differ`), so at a visit's first decision the
frozen policy can value the two situations differently.

Not proved here or anywhere: that an agent of the executed type that steps by the declared rule
meets either promise.
-/

namespace AcornVerif.CurrentForkedTargetRungLearns
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung AcornVerif.CurrentExplorer
open AcornVerif.CurrentForkedTarget AcornVerif.CurrentForkedTargetRung
open AcornVerif.CurrentForkedTargetBoth AcornVerif.CurrentForkedTargetRungBoth
open AcornVerif.CurrentForkedTargetRule

/-- What an agent that ignores its observation still reads of a percept: its reward word and its
achievement flag. -/
def rewardAndFlag (percept : Percept Grid.interface) : Binary32 × Bool :=
  (percept.reward, percept.frame.achieved)

/-! ## What mastery of a grid excludes -/

/-- **No agent that keeps nothing masters a grid at the sharp covering bound**, whatever the
limit, the horizon, the returns and the predicate. -/
theorem rung_grid_need (mode : TaskFeatureMode) {agent : Kernel.Agent Grid.interface}
    (free : Kernel.ExperienceFree agent) (limit horizon returns : ℕ)
    (admits : (rungForks mode).Index → (ℕ → Bool) → ℕ → Prop) :
    ¬ Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 49
      (firstTarget mode witnessLive duskLive 7) (secondTarget mode witnessLive duskLive 7)
      limit horizon returns admits agent :=
  forked_need_grid mode witnessLive duskLive 7 free limit horizon returns admits

/-- **No agent that goes by its clock, its reward words and its achievement flags masters a
grid**, at any bound, keys, limit, horizon, returns and predicate. -/
theorem rung_grid_blind (mode : TaskFeatureMode) {agent : Kernel.Agent Grid.interface}
    (blind : Kernel.FeedbackDriven rewardAndFlag agent) (bound limit horizon returns : ℕ)
    {κ μ : Type} (one : (rungForks mode).Index → κ) (two : (rungForks mode).Index → μ)
    (admits : (rungForks mode).Index → (ℕ → Bool) → ℕ → Prop) :
    ¬ Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 bound one two limit horizon
      returns admits agent :=
  forked_blind_grid mode witnessLive duskLive 7 dusk_carried blind bound limit horizon returns
    one two admits

/-- **The chooser over that feedback, made to act otherwise only where the class never looks,
masters no grid.** A chooser whose preference and memory read the percept through the reward
word and the achievement flag, made to hold a resting preference on a set of percepts that no
member of the rung's class delivers, masters no grid at any bound, keys, limit, horizon, returns
and predicate. -/
theorem rung_grid_hybrid (mode : TaskFeatureMode) {E Core V : Type}
    (select : E → V → Kernel.Act Grid.interface × E) (core : Core) (seed : E)
    (prefer : Core → Binary32 × Bool → V)
    (advance : Core → Binary32 × Bool → Kernel.Act Grid.interface → Core)
    (alien : Percept Grid.interface → Prop) [DecidablePred alien] (rest : V)
    (never : ∀ state : Option (Live witnessConfig),
      ¬ alien ((gridWorld witnessConfig mode).percept state))
    (bound limit horizon returns : ℕ) {κ μ : Type} (one : (rungForks mode).Index → κ)
    (two : (rungForks mode).Index → μ)
    (admits : (rungForks mode).Index → (ℕ → Bool) → ℕ → Prop) :
    ¬ Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 bound one two limit horizon
      returns admits
      (Kernel.chooser select core seed
        (Kernel.aloof alien rest (fun inner percept => prefer inner (rewardAndFlag percept)))
        (fun inner percept action => advance inner (rewardAndFlag percept) action)) :=
  Kernel.aloof_mastersGrid select core seed prefer advance alien rest
    (fun _ state => never state) (forked_mute mode witnessLive duskLive 7 dusk_carried)
    (forked_apart mode witnessLive duskLive 7)

/-! ## What mastery of a grid gives -/

variable {mode : TaskFeatureMode} {agent : Kernel.Agent Grid.interface} {bound limit horizon
  returns : ℕ} {admits : (rungForks mode).Index → (ℕ → Bool) → ℕ → Prop}

/-- **An agent that masters a grid reads what it perceives.** There are an order, a visit, a
member and a step of that visit at which the agent's actions differ between the two runs that
differ in that visit's situation alone, while its memory at the visit's start is the same in
both. -/
theorem grid_reads {κ μ : Type} {one : (rungForks mode).Index → κ}
    {two : (rungForks mode).Index → μ}
    (masters : Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 bound one two limit
      horizon returns admits agent) :
    ∃ (order : ℕ → Bool) (visit : ℕ) (pair : (rungForks mode).Index) (step : ℕ),
      step < 7 ∧
        Kernel.turnMemory ((rungForks mode).world pair) ((rungForks mode).start pair)
            (Function.update order visit false) 7 agent visit =
          Kernel.turnMemory ((rungForks mode).world pair) ((rungForks mode).start pair)
            (Function.update order visit true) 7 agent visit ∧
        Kernel.actionAt
            (Kernel.turns ((rungForks mode).world pair) ((rungForks mode).start pair)
              (Function.update order visit false) 7) agent
            (Kernel.turnStart ((rungForks mode).world pair) ((rungForks mode).start pair)
              (Function.update order visit false) 7 0) (visit * (7 + 1) + step) ≠
          Kernel.actionAt
            (Kernel.turns ((rungForks mode).world pair) ((rungForks mode).start pair)
              (Function.update order visit true) 7) agent
            (Kernel.turnStart ((rungForks mode).world pair) ((rungForks mode).start pair)
              (Function.update order visit true) 7 0) (visit * (7 + 1) + step) := by
  obtain ⟨order, visit, pair, -, solved⟩ := masters.solves
  obtain ⟨step, short, differ⟩ := Kernel.turn_differs
    (forked_apart mode witnessLive duskLive 7) order agent visit pair solved
  exact ⟨order, visit, pair, step, short,
    (Kernel.turnMemory_sides _ _ order 7 _ visit false).trans
      (Kernel.turnMemory_sides _ _ order 7 _ visit true).symm, differ⟩

/-- **An agent that masters a grid has met both situations.** There are an order, a visit and a
grid of more than 49 first targets and more than 49 second targets such that, under every second
target of the grid, some first target of the grid is one the agent had already solved, in that
member's run, on an earlier visit of the first situation; and under every first target, some
second target is one it had already solved on an earlier visit of the second situation. What it
met in one situation did not supply the other's answer. -/
theorem grid_experienced
    (masters : Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 49
      (firstTarget mode witnessLive duskLive 7) (secondTarget mode witnessLive duskLive 7)
      limit horizon returns admits agent) :
    ∃ (order : ℕ → Bool) (visit : ℕ)
      (firsts : Finset (feasibleFind witnessConfig mode witnessLive 7).Index)
      (seconds : Finset (feasibleFind witnessConfig mode duskLive 7).Index),
      49 < firsts.card ∧ 49 < seconds.card ∧
      (∀ two ∈ seconds, ∃ pair : (rungForks mode).Index,
        secondTarget mode witnessLive duskLive 7 pair = two ∧
          firstTarget mode witnessLive duskLive 7 pair ∈ firsts ∧
          ∃ earlier, earlier < visit ∧ order earlier = false ∧
            Kernel.SolvesTurn (rungForks mode) (rungForkGoals mode) 7 order agent earlier
              pair) ∧
      (∀ one ∈ firsts, ∃ pair : (rungForks mode).Index,
        firstTarget mode witnessLive duskLive 7 pair = one ∧
          secondTarget mode witnessLive duskLive 7 pair ∈ seconds ∧
          ∃ earlier, earlier < visit ∧ order earlier = true ∧
            Kernel.SolvesTurn (rungForks mode) (rungForkGoals mode) 7 order agent earlier
              pair) := by
  obtain ⟨order, visit, firsts, seconds, -, manyFirst, manySecond, each⟩ := masters
  refine ⟨order, visit, firsts, seconds, manyFirst, manySecond,
    fun two inSeconds => ?_, fun one inFirsts => ?_⟩
  · by_contra none
    have few := grid_first_experience mode witnessLive duskLive 7 agent order visit firsts two
      (fun own inFirsts => by
        obtain ⟨pair, isOne, isTwo, solved⟩ := each own inFirsts two inSeconds
        exact ⟨pair, isOne, isTwo, (solved false).1, fun earlier early side found =>
          none ⟨pair, isTwo, by rw [isOne]; exact inFirsts, earlier, early, side, found⟩⟩)
    omega
  · by_contra none
    have few := grid_second_experience mode witnessLive duskLive 7 agent order visit seconds one
      (fun own inSeconds => by
        obtain ⟨pair, isOne, isTwo, solved⟩ := each one inFirsts own inSeconds
        exact ⟨pair, isTwo, isOne, (solved true).1, fun earlier early side found =>
          none ⟨pair, isOne, by rw [isTwo]; exact inSeconds, earlier, early, side, found⟩⟩)
    omega

/-! ## What the rule adds -/

/-- **On a calm visit the agent's actions are greedy choices among its values.** For a
construction that steps by the declared rule: on a calm visit of a member's run under an order,
each of the seven actions the world takes is the action of the persistent draw that began no
run, over the policy the primitive controller freezes from its weights at that decision's
frame. -/
theorem calm_turn_greedy (planning : PlanningSelection) (rule : StepsByRule planning)
    (pair : (rungForks (rungConstruction planning).profile.taskMode).Index) (order : ℕ → Bool)
    (visit : ℕ) (calm : TurnCalm planning pair order visit) (step : ℕ) (short : step < 7) :
    Kernel.actionAt
        (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
          ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7)
        (executedAgent (rungConstruction planning).initial.agent)
        (Kernel.turnStart ((rungForks (rungConstruction planning).profile.taskMode).world pair)
          ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7 0)
        (visit * (7 + 1) + step) =
      (((Kernel.memoryAt
            (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7)
            (executedAgent (rungConstruction planning).initial.agent)
            (Kernel.turnStart
              ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7 0)
            (visit * (7 + 1) + step)).control.runtime.lifecycle.consumers.control.snapshot
          ((Kernel.memoryAt
            (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7)
            (executedAgent (rungConstruction planning).initial.agent)
            (Kernel.turnStart
              ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7 0)
            (visit * (7 + 1) + step)).advanceClock.frame
            (Kernel.perceptAt
              (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
                ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7)
              (executedAgent (rungConstruction planning).initial.agent)
              (Kernel.turnStart
                ((rungForks (rungConstruction planning).profile.taskMode).world pair)
                ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7
                0)
              (visit * (7 + 1) + step)).frame).active declaredRate).drawPersistent
        (explorerOf (Kernel.memoryAt
            (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7)
            (executedAgent (rungConstruction planning).initial.agent)
            (Kernel.turnStart
              ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7 0)
            (visit * (7 + 1) + step)).control).rng).1.action :=
  calm_action planning rule _ _ (calm step short)

/-! ## That the two promises can be met -/

/-- **The witness meets both promises.** For every task mode, the agent
`AcornVerif.CurrentForkedTargetRungBoth.gridWitness` masters a grid before visit 576 with 288
later occasions before visit 1728, under the predicate that admits every visit, and keeps before
visit 1728 on the visits of every predicate. It is a kernel agent built for the purpose, which
records a rewarded visit's actions for each situation and replays them. -/
theorem witness_promises (mode : TaskFeatureMode) :
    Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 49
        (firstTarget mode witnessLive duskLive 7) (secondTarget mode witnessLive duskLive 7)
        576 1728 288 (fun _ _ _ => True) gridWitness ∧
      ∀ admits, Kernel.KeepsOn (rungForks mode) (rungForkGoals mode) 7 1728 admits
        gridWitness :=
  ⟨(grid_witness_masters mode 1728 288 (by decide)).mono (by decide),
    fun admits => (grid_witness_keeps mode 1728).on admits⟩

end AcornVerif.CurrentForkedTargetRungLearns
