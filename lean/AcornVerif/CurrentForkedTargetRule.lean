import AcornVerif.CurrentDeclaredStep
import AcornVerif.CurrentForkedTargetRung

namespace AcornVerif.CurrentForkedTargetRule
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung AcornVerif.CurrentExplorer
open AcornVerif.CurrentForkedTarget AcornVerif.CurrentForkedTargetRung
open AcornVerif.CurrentPreReward
open AcornVerif.CurrentDeclaredStep (perceivedActive)

def StepsByRule (planning : PlanningSelection) : Prop :=
  CurrentDeclaredStep.StepsByRule Grid.interface (rungConstruction planning).profile
    (rungConstruction planning).config (rungConstruction planning).criterion
    (rungConstruction planning).dimension (rungConstruction planning).planning

def StartsCold (planning : PlanningSelection) : Prop :=
  (rungConstruction planning).initial.agent.control =
    TemporalControl.initial Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension

theorem steps_met (planning : PlanningSelection) : StepsByRule planning :=
  CurrentDeclaredStep.act_steps rfl

theorem starts_cold_met (planning : PlanningSelection) : StartsCold planning := rfl

theorem steps_act (planning : PlanningSelection) (rule : StepsByRule planning)
    (agent : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning)
    (percept : Percept Grid.interface) :
    (agent.act percept).2.action = ((explorerOf agent.control).stepOver
        (agent.control.runtime.lifecycle.consumers.control.snapshot
          (perceivedActive agent.control percept.frame) declaredRate)).1 ∧
      explorerOf (agent.act percept).1.control = ((explorerOf agent.control).stepOver
        (agent.control.runtime.lifecycle.consumers.control.snapshot
          (perceivedActive agent.control percept.frame) declaredRate)).2 :=
  CurrentDeclaredStep.StepsByRule.draws rule rfl rfl agent percept

theorem cold_until_rewarded (planning : PlanningSelection) (rule : StepsByRule planning)
    (cold : StartsCold planning) (world : Kernel.World Grid.interface) (start : world.State)
    (time : ℕ)
    (unpaid : ∀ earlier, earlier < time →
      (Kernel.perceptAt world (executedAgent (rungConstruction planning).initial.agent) start
        earlier).reward.isZero = true) :
    Kernel.actionAt world (executedAgent (rungConstruction planning).initial.agent) start time =
      (Explorer.cold Grid.interface.actions (rungConstruction planning).config.seed).actionAt
        time := by
  have rest : Quiet (rungConstruction planning).initial.agent.control := by
    rw [cold]
    exact Quiet.initial
  have explorer : explorerOf (rungConstruction planning).initial.agent.control =
      Explorer.cold Grid.interface.actions (rungConstruction planning).config.seed := by
    rw [cold]
    rfl
  have followed := (CurrentDeclaredStep.StepsByRule.quiet_actions rule rfl rfl
    (rungConstruction planning).initial.agent rest world start time unpaid).2.2
  rw [explorer] at followed
  exact followed

def CalmAt (planning : PlanningSelection)
    (agent : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning)
    (percept : Percept Grid.interface) : Prop :=
  (explorerOf agent.control).run.bind ExploratoryRun.serve = none ∧
    ((agent.control.runtime.lifecycle.consumers.control.snapshot
        (perceivedActive agent.control percept.frame) declaredRate).drawPersistent
      (explorerOf agent.control).rng).1.explored = false

def TurnCalm (planning : PlanningSelection)
    (pair : (rungForks (rungConstruction planning).profile.taskMode).Index) (order : ℕ → Bool)
    (visit : ℕ) : Prop :=
  ∀ step, step < 7 →
    CalmAt planning
      (Kernel.memoryAt
        (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
          ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7)
        (executedAgent (rungConstruction planning).initial.agent)
        (Kernel.turnStart ((rungForks (rungConstruction planning).profile.taskMode).world pair)
          ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7 0)
        (visit * (7 + 1) + step))
      (Kernel.perceptAt
        (Kernel.turns ((rungForks (rungConstruction planning).profile.taskMode).world pair)
          ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7)
        (executedAgent (rungConstruction planning).initial.agent)
        (Kernel.turnStart ((rungForks (rungConstruction planning).profile.taskMode).world pair)
          ((rungForks (rungConstruction planning).profile.taskMode).start pair) order 7 0)
        (visit * (7 + 1) + step))

theorem calm_action (planning : PlanningSelection) (rule : StepsByRule planning)
    (agent : Agent Grid.interface (rungConstruction planning).profile
      (rungConstruction planning).config (rungConstruction planning).criterion
      (rungConstruction planning).dimension (rungConstruction planning).planning)
    (percept : Percept Grid.interface) (calm : CalmAt planning agent percept) :
    (agent.act percept).2.action =
      ((agent.control.runtime.lifecycle.consumers.control.snapshot
          (perceivedActive agent.control percept.frame) declaredRate).greedy
        (explorerOf agent.control).rng.nextF64.2).1 := by
  rw [(steps_act planning rule agent percept).1]
  unfold Explorer.stepOver
  rw [calm.1]
  exact ((CurrentTemporal.persistent_draw _ _).2.1 calm.2).2

end AcornVerif.CurrentForkedTargetRule
