import AcornVerif.CurrentForkedTargetFrames
import AcornVerif.CurrentForkedTargetRule
import AcornVerif.CurrentForkedTargetRungBoth

namespace AcornVerif.CurrentForkedTargetRungLearns
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung AcornVerif.CurrentExplorer
open AcornVerif.CurrentForkedTarget AcornVerif.CurrentForkedTargetRung
open AcornVerif.CurrentForkedTargetBoth AcornVerif.CurrentForkedTargetRungBoth
open AcornVerif.CurrentForkedTargetRule

def rewardAndFlag (percept : Percept Grid.interface) : Binary32 × Bool :=
  (percept.reward, percept.frame.achieved)

theorem rung_grid_need (mode : TaskFeatureMode) {agent : Kernel.Agent Grid.interface}
    (free : Kernel.ExperienceFree agent) (limit horizon returns : ℕ)
    (admits : (rungForks mode).Index → (ℕ → Bool) → ℕ → Prop) :
    ¬ Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 49
      (firstTarget mode witnessLive duskLive 7) (secondTarget mode witnessLive duskLive 7)
      limit horizon returns admits agent :=
  forked_need_grid mode witnessLive duskLive 7 free limit horizon returns admits

theorem rung_grid_blind (mode : TaskFeatureMode) {agent : Kernel.Agent Grid.interface}
    (blind : Kernel.FeedbackDriven rewardAndFlag agent) (bound limit horizon returns : ℕ)
    {κ μ : Type} (one : (rungForks mode).Index → κ) (two : (rungForks mode).Index → μ)
    (admits : (rungForks mode).Index → (ℕ → Bool) → ℕ → Prop) :
    ¬ Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 bound one two limit horizon
      returns admits agent :=
  forked_blind_grid mode witnessLive duskLive 7 dusk_carried blind bound limit horizon returns
    one two admits

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

variable {mode : TaskFeatureMode} {agent : Kernel.Agent Grid.interface} {bound limit horizon
  returns : ℕ} {admits : (rungForks mode).Index → (ℕ → Bool) → ℕ → Prop}

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
          (CurrentDeclaredStep.perceivedActive (Kernel.memoryAt
            (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7)
            (executedAgent (rungConstruction planning).initial.agent)
            (Kernel.turnStart
              ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7 0)
            (visit * (7 + 1) + step)).control
            (Kernel.perceptAt
              (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
                ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7)
              (executedAgent (rungConstruction planning).initial.agent)
              (Kernel.turnStart
                ((rungForks (rungConstruction planning).profile.taskMode).world pair)
                ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7
                0)
              (visit * (7 + 1) + step)).frame) declaredRate).greedy
        (explorerOf (Kernel.memoryAt
            (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7)
            (executedAgent (rungConstruction planning).initial.agent)
            (Kernel.turnStart
              ((rungForks (rungConstruction planning).profile.taskMode).world pair)
              ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7 0)
            (visit * (7 + 1) + step)).control).rng.nextF64.2).1 :=
  calm_action planning rule _ _ (calm step short)

theorem starts_perceived (planning : PlanningSelection)
    (agent : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning)
    (first second : Host.Position) :
    ∃ slot,
      slot ∈ (CurrentDeclaredStep.perceivedActive agent.control
        ((gridWorld witnessConfig (rungConstruction planning).profile.taskMode).percept
          (member witnessLive first)).frame).indices ∧
      slot ∉ (CurrentDeclaredStep.perceivedActive agent.control
        ((gridWorld witnessConfig (rungConstruction planning).profile.taskMode).percept
          (member duskLive second)).frame).indices :=
  CurrentForkedTargetFrames.starts_differ planning agent first second

theorem witness_promises (mode : TaskFeatureMode) :
    Kernel.MastersGridBy (rungForks mode) (rungForkGoals mode) 7 49
        (firstTarget mode witnessLive duskLive 7) (secondTarget mode witnessLive duskLive 7)
        576 1728 288 (fun _ _ _ => True) gridWitness ∧
      ∀ admits, Kernel.KeepsOn (rungForks mode) (rungForkGoals mode) 7 1728 admits
        gridWitness :=
  ⟨(grid_witness_masters mode 1728 288 (by decide)).mono (by decide),
    fun admits => (grid_witness_keeps mode 1728).on admits⟩

end AcornVerif.CurrentForkedTargetRungLearns
