import AcornVerif.CurrentConcealedTargetRungLearns
import AcornVerif.Twin

namespace AcornVerif.CurrentConcealedTargetTwin
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentGoals AcornVerif.CurrentGridWorld AcornVerif.CurrentConcealedTarget
open AcornVerif.CurrentConcealedTargetRung

variable {config : Host.WorldConfig}

def Shadowed (target : Host.Position) (state shadow : Option (Live config)) : Prop :=
  (state = none ∧ shadow = none) ∨
  ∃ found base, state = some found ∧ shadow = some base ∧
    physical found.world = physical base.world ∧
    found.world.goal = some (.find target) ∧ base.world.goal = some (.find nowhere) ∧
    base.carried.events.done = false ∧ base.carried.reward = ⟨0⟩ ∧
    (found.world.goalSatisfied = false → found.carried = base.carried) ∧
    (found.world.goalSatisfied = true →
      found.carried = ⟨{ base.carried.events with done := true }, ⟨0x3f800000⟩⟩)

def rebuilt (mode : TaskFeatureMode) (shadow : Option (Live config)) (reward : Binary32) :
    Percept Grid.interface :=
  match shadow with
  | none => percept mode (none : Option (Live config))
  | some base =>
    if reward = ⟨0x3f800000⟩ then
      Grid.percept mode
        (sensed (base.world.setGoal (.find base.world.body.position.position)))
        ⟨0x3f800000⟩ true
    else percept mode (some base)

theorem shadowed_start (live : Live config) (target : Host.Position)
    (outside : ¬ InGoalBox target live.world.body.position.position)
    (calm : live.carried.events.done = false) (unpaid : live.carried.reward = ⟨0⟩) :
    Shadowed target (member live target) (member live nowhere) := by
  have unmet : (live.world.setGoal (.find target)).goalSatisfied = false := by
    cases met : (live.world.setGoal (.find target)).goalSatisfied with
    | false => rfl
    | true => exact absurd ((find_goal_iff _ target rfl).mp met) outside
  exact Or.inr ⟨⟨live.world.setGoal (.find target), live.carried⟩,
    ⟨live.world.setGoal (.find nowhere), live.carried⟩, rfl, rfl, rfl, rfl, rfl, calm, unpaid,
    fun _ => rfl, fun met => absurd (unmet.symm.trans met) Bool.false_ne_true⟩

theorem shadowed_step (mode : TaskFeatureMode) (target : Host.Position)
    (state shadow : Option (Live config)) (action : Kernel.Act Grid.interface)
    (held : Shadowed target state shadow) :
    Shadowed target ((gridWorld config mode).step state action)
      ((gridWorld config mode).step shadow action) := by
  rcases held with ⟨rfl, rfl⟩ | ⟨found, base, rfl, rfl, twins, goal, goalBase, -, -, -, -⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · change Shadowed target (advance found action) (advance base action)
    have same := (step_physical found.world (Host.Action.fromIndex action.val)).symm.trans
      ((congrArg (fun world => Host.World.step world (Host.Action.fromIndex action.val))
        twins).trans (step_physical base.world (Host.Action.fromIndex action.val)))
    cases stepped : found.world.step (Host.Action.fromIndex action.val) with
    | error refusal =>
      cases steppedBase : base.world.step (Host.Action.fromIndex action.val) with
      | error refusalBase =>
        exact Or.inl ⟨by simp only [advance, stepped], by simp only [advance, steppedBase]⟩
      | ok pairBase =>
        simp only [stepped, steppedBase] at same
        cases same
    | ok pair =>
      obtain ⟨world, events⟩ := pair
      cases steppedBase : base.world.step (Host.Action.fromIndex action.val) with
      | error refusalBase =>
        simp only [stepped, steppedBase] at same
        cases same
      | ok pairBase =>
        obtain ⟨worldBase, eventsBase⟩ := pairBase
        simp only [stepped, steppedBase, Except.ok.injEq, Prod.mk.injEq] at same
        obtain ⟨twinsNext, eventsSame⟩ := same
        rw [advance_ok found _ world events stepped,
          advance_ok base _ worldBase eventsBase steppedBase]
        have goalNext : world.goal = some (.find target) :=
          (Host.World.step_goal _ _ _ _ stepped).1.trans goal
        have goalBaseNext : worldBase.goal = some (.find nowhere) :=
          (Host.World.step_goal _ _ _ _ steppedBase).1.trans goalBase
        have completed : events.done = world.goalSatisfied :=
          Host.World.step_completion _ _ _ _ stepped
        have doneBase : eventsBase.done = false :=
          (Host.World.step_completion _ _ _ _ steppedBase).trans
            (nowhere_unmet worldBase goalBaseNext)
        have cleared : { events with done := false } = eventsBase :=
          eventsSame.trans (clear_done eventsBase doneBase)
        refine Or.inr ⟨⟨world, events.raw⟩, ⟨worldBase, eventsBase.raw⟩, rfl, rfl, twinsNext,
          goalNext, goalBaseNext, doneBase, ?_, ?_, ?_⟩
        · change eventsBase.reward = ⟨0⟩
          unfold Host.StepResult.reward
          rw [doneBase]
          rfl
        · intro unmet
          have equal : events = eventsBase :=
            (clear_done events (completed.trans unmet)).symm.trans cleared
          rw [equal]
        · intro met
          have finished : events.done = true := completed.trans met
          change events.raw = ⟨{ eventsBase with done := true }, ⟨0x3f800000⟩⟩
          rw [← cleared]
          obtain ⟨flag, moved, harvested, ate, crafted, exhausted, picked⟩ := events
          have flagged : flag = true := finished
          subst flagged
          rfl

theorem inGoalBox_self (position : Host.Position) : InGoalBox position position := by
  unfold InGoalBox
  simp only [Int.sub_self, Int.natAbs_zero]
  exact ⟨Nat.zero_le _, Nat.zero_le _⟩

theorem shadowed_percept (mode : TaskFeatureMode) (target : Host.Position)
    (state shadow : Option (Live config)) (held : Shadowed target state shadow) :
    (gridWorld config mode).percept state =
      rebuilt mode shadow ((gridWorld config mode).percept state).reward := by
  rcases held with ⟨rfl, rfl⟩ | ⟨found, base, rfl, rfl, twins, goal, goalBase, -, unpaid, quiet,
    loud⟩
  · rfl
  · change Grid.percept mode (sensed found.world) found.carried.reward
        found.carried.events.done = rebuilt mode (some base) found.carried.reward
    cases met : found.world.goalSatisfied with
    | false =>
      have task : found.world.taskObservation = base.world.taskObservation := by
        rw [find_task found.world target goal, find_task base.world nowhere goalBase, met,
          nowhere_unmet base.world goalBase]
      have other : ¬ base.carried.reward = (⟨0x3f800000⟩ : Binary32) := by
        rw [unpaid]
        decide
      rw [quiet met, sensed_twins found.world base.world twins task]
      unfold rebuilt
      dsimp only
      split
      · rename_i equal
        exact absurd equal other
      · rfl
    | true =>
      have inside : (base.world.setGoal
          (.find base.world.body.position.position)).goalSatisfied = true :=
        (find_goal_iff _ _ rfl).mpr (inGoalBox_self _)
      have task : found.world.taskObservation = (base.world.setGoal
          (.find base.world.body.position.position)).taskObservation := by
        rw [find_task found.world target goal, find_task _ _ rfl, met, inside]
      rw [loud met, sensed_twins found.world
        (base.world.setGoal (.find base.world.body.position.position)) twins task]
      unfold rebuilt
      dsimp only
      rfl

theorem rung_twin (mode : TaskFeatureMode) (agent : Kernel.Agent Grid.interface) :
    ∃ twin : Kernel.Agent Grid.interface,
      Kernel.Stepped (fun percept : Percept Grid.interface => percept.reward) twin ∧
      (∀ (count : ℕ) (index : (feasibleFind witnessConfig mode witnessLive 7).Index),
        Kernel.SolvesOnVisit (feasibleFind witnessConfig mode witnessLive 7)
            (fun _ => completion witnessConfig mode 7) 7 twin count index ↔
          Kernel.SolvesOnVisit (feasibleFind witnessConfig mode witnessLive 7)
            (fun _ => completion witnessConfig mode 7) 7 agent count index) ∧
      ∀ (bound limit horizon lapses : ℕ)
        (counted : List (feasibleFind witnessConfig mode witnessLive 7).Index),
        (Kernel.SeparatesBy (feasibleFind witnessConfig mode witnessLive 7)
            (fun _ => completion witnessConfig mode 7) 7 bound counted limit twin ↔
          Kernel.SeparatesBy (feasibleFind witnessConfig mode witnessLive 7)
            (fun _ => completion witnessConfig mode 7) 7 bound counted limit agent) ∧
        (Kernel.RetainsBut (feasibleFind witnessConfig mode witnessLive 7)
            (fun _ => completion witnessConfig mode 7) 7 horizon lapses twin ↔
          Kernel.RetainsBut (feasibleFind witnessConfig mode witnessLive 7)
            (fun _ => completion witnessConfig mode 7) 7 horizon lapses agent) := by
  have first : ∀ index : (feasibleFind witnessConfig mode witnessLive 7).Index,
      Shadowed index.1.1 ((feasibleFind witnessConfig mode witnessLive 7).start index)
        (member witnessLive nowhere) :=
    fun index => shadowed_start witnessLive index.1.1 index.1.2 rfl rfl
  refine ⟨Kernel.twin (fun percept : Percept Grid.interface => percept.reward) agent
      (Kernel.visits (gridWorld witnessConfig mode) (member witnessLive nowhere) 7)
      (Kernel.visitStart (gridWorld witnessConfig mode) (member witnessLive nowhere) 7)
      (fun shadow => rebuilt mode shadow.1),
    Kernel.twin_stepped _ _ _ _ _, ?_, ?_⟩
  · exact Kernel.twin_solvesOnVisit (fun percept : Percept Grid.interface => percept.reward)
      agent (gridWorld witnessConfig mode) (member witnessLive nowhere) (rebuilt mode)
      (feasibleFind witnessConfig mode witnessLive 7) (fun _ => completion witnessConfig mode 7)
      7 (fun index => Shadowed index.1.1) first
      (fun index state shadow action held => shadowed_step mode index.1.1 state shadow action held)
      (fun index state shadow held => shadowed_percept mode index.1.1 state shadow held)
  · intro bound limit horizon lapses counted
    exact Kernel.twin_clauses (fun percept : Percept Grid.interface => percept.reward)
      agent (gridWorld witnessConfig mode) (member witnessLive nowhere) (rebuilt mode)
      (feasibleFind witnessConfig mode witnessLive 7) (fun _ => completion witnessConfig mode 7)
      7 (fun index => Shadowed index.1.1) first
      (fun index state shadow action held => shadowed_step mode index.1.1 state shadow action held)
      (fun index state shadow held => shadowed_percept mode index.1.1 state shadow held)
      bound limit horizon lapses counted

theorem learns_twin (learns : Targets.CurrentConcealedTargetRung.rung_learns) :
    ∃ (planning : PlanningSelection)
      (counted : List (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode
        witnessLive 7).Index)
      (twin : Kernel.Agent Grid.interface),
      Kernel.Stepped (fun percept : Percept Grid.interface => percept.reward) twin ∧
        counted.Nodup ∧
        Kernel.SeparatesBy
          (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
          (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
          98 counted 288 twin ∧
        Kernel.RetainsBut
          (feasibleFind witnessConfig (rungConstruction planning).profile.taskMode witnessLive 7)
          (fun _ => completion witnessConfig (rungConstruction planning).profile.taskMode 7) 7
          864 144 twin := by
  obtain ⟨-, -, -, -, -, planning, counted, -, -, -, -, -, distinct, separates, retains⟩ := learns
  obtain ⟨twin, stepped, -, clauses⟩ := rung_twin (rungConstruction planning).profile.taskMode
    (executedAgent (rungConstruction planning).initial.agent)
  exact ⟨planning, counted, twin, stepped, distinct,
    (clauses 98 288 864 144 counted).1.mpr separates,
    (clauses 98 288 864 144 counted).2.mpr retains⟩

end AcornVerif.CurrentConcealedTargetTwin
