/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentRunner
import AcornVerif.CurrentStep

/-!
# Executed goal guarantees

Each goal family's completion predicate is `Goal.observe` followed by
`TaskObservation.satisfied`, the predicate the world reports and the attempt
stops on. These theorems state what that executed predicate reads, for every
goal, world, action and agent callback.

A reach goal reads the body's position alone (`reach_satisfied_iff`), and so does a
concealed target, in the same box (`find_satisfied_iff`); its observation is the one cue
of its family and whether it is satisfied (`find_observe`). A craft goal
reads tool ownership and a collect goal the held count (`craft_satisfied`,
`collect_satisfied_iff`); since no step removes a tool or lowers gold, a craft or
gold goal achieved once is achieved again at the first step of every later visit
(`absorbing_revisit`). A survive goal reads the clock alone: an action sequence
satisfies it exactly when its length has reached the required duration
(`survive_actions`), and a tick of an attempt reports completion exactly when the
attempt's step count has (`survive_tick`).

The survive theorems assume the wrapping 64-bit clock has not wrapped since the
goal was installed, and all assume the world steps succeed. `survive_tick` is a
per-tick statement; no theorem here composes ticks over an attempt or its cap. No
theorem here shows that a reach, collect or craft goal is feasible;
`AcornVerif.CurrentCertificates` decides feasibility for one seed from a certificate.
-/
namespace AcornVerif.CurrentGoals
open Acorn Acorn.Host
open AcornVerif.CurrentStep

variable {order : StepOrder}

/-- A word built from a count below 2^64 is zero exactly when the count is. -/
theorem toUInt64_eq_zero (count : Nat) (bound : count < 2 ^ 64) :
    count.toUInt64 = 0 ↔ count = 0 := by
  constructor
  · intro zero
    have word := congrArg UInt64.toNat zero
    rw [show count.toUInt64 = UInt64.ofNat count from rfl, UInt64.toNat_ofNat_of_lt' bound] at word
    simpa using word
  · rintro rfl
    rfl

/-- A word built from a count below 2^32 is zero exactly when the count is. -/
theorem toUInt32_eq_zero (count : Nat) (bound : count < 2 ^ 32) :
    count.toUInt32 = 0 ↔ count = 0 := by
  constructor
  · intro zero
    have word := congrArg UInt32.toNat zero
    rw [show count.toUInt32 = UInt32.ofNat count from rfl, UInt32.toNat_ofNat_of_lt' bound] at word
    simpa using word
  · rintro rfl
    rfl

/-! ## What each goal reads -/

/-- A reach goal's box: the positions within the reach radius of the target on both axes. -/
def InGoalBox (target position : Position) : Prop :=
  (target.x.val - position.x.val).natAbs ≤ FeatureConstants.reachRadius ∧
    (target.y.val - position.y.val).natAbs ≤ FeatureConstants.reachRadius

/-- Reaching is a property of position only: a reach goal is satisfied exactly in its
box, whatever the inventory and the elapsed time. -/
theorem reach_satisfied_iff (target position : Position) (inventory : Inventory)
    (elapsed : UInt64) :
    ((Goal.reach target).observe position inventory elapsed).satisfied = true ↔
      InGoalBox target position := by
  simp only [Goal.observe, TaskObservation.satisfied, ReachRelation.distance,
    ReachRelation.between, InGoalBox, FeatureConstants.reachRadius, beq_iff_eq]
  omega

/-- A craft goal is satisfied exactly when its tool is owned. -/
theorem craft_satisfied (tool : Craftable) (position : Position) (inventory : Inventory)
    (elapsed : UInt64) :
    ((Goal.craft tool).observe position inventory elapsed).satisfied = inventory.owns tool := by
  simp [Goal.observe, TaskObservation.satisfied]

/-- A collect goal is satisfied exactly when the inventory holds the requested count. -/
theorem collect_satisfied_iff (item : Item) (count : UInt32) (position : Position)
    (inventory : Inventory) (elapsed : UInt64) :
    ((Goal.collect item count).observe position inventory elapsed).satisfied = true ↔
      count.toNat ≤ (inventory.count item).toNat := by
  simp only [Goal.observe, TaskObservation.satisfied, beq_iff_eq]
  rw [toUInt32_eq_zero _ (by have := count.toNat_lt; omega)]
  omega

/-- A survive goal is satisfied exactly when the required time has elapsed. -/
theorem survive_satisfied_iff (required : UInt64) (position : Position) (inventory : Inventory)
    (elapsed : UInt64) :
    ((Goal.survive required).observe position inventory elapsed).satisfied = true ↔
      required.toNat ≤ elapsed.toNat := by
  simp only [Goal.observe, TaskObservation.satisfied, beq_iff_eq]
  rw [toUInt64_eq_zero _ (by have := required.toNat_lt; omega)]
  omega

/-- The world's completion flag is its installed goal's predicate on the body's
position, the inventory and the saturating time since installation. -/
theorem goalSatisfied_eq {config : WorldConfig} (world : World config) (goal : Goal)
    (installed : world.goal = some goal) :
    world.goalSatisfied = (goal.observe world.body.position.position world.body.inventory
      (world.time.toNat - world.goalStart.toNat).toUInt64).satisfied := by
  simp only [World.goalSatisfied, World.taskObservation, installed]

/-- With a reach goal installed, the world's completion flag reads the body's position
alone: it holds exactly when the body is in the goal box. -/
theorem reach_goal_iff {config : WorldConfig} (world : World config) (target : Position)
    (installed : world.goal = some (.reach target)) :
    world.goalSatisfied = true ↔ InGoalBox target world.body.position.position := by
  rw [goalSatisfied_eq world _ installed]
  exact reach_satisfied_iff _ _ _ _

/-- A concealed target is satisfied exactly in its box, whatever the inventory and the elapsed
time: the box of a reach goal for the same target. -/
theorem find_satisfied_iff (target position : Position) (inventory : Inventory)
    (elapsed : UInt64) :
    ((Goal.find target).observe position inventory elapsed).satisfied = true ↔
      InGoalBox target position := by
  simp only [Goal.observe, TaskObservation.satisfied, ReachRelation.distance,
    ReachRelation.between, InGoalBox, FeatureConstants.reachRadius, beq_iff_eq]
  omega

/-- The observation of a concealed target is the one cue of its family and whether it is
satisfied: nothing else of the target. -/
theorem find_observe (target position : Position) (inventory : Inventory) (elapsed : UInt64) :
    (Goal.find target).observe position inventory elapsed =
      .find (Rng.hash3 5 0 0) ((Goal.find target).observe position inventory elapsed).satisfied :=
  rfl

/-- With a concealed target installed, the world's completion flag reads the body's position
alone: it holds exactly when the body is in the goal box. -/
theorem find_goal_iff {config : WorldConfig} (world : World config) (target : Position)
    (installed : world.goal = some (.find target)) :
    world.goalSatisfied = true ↔ InGoalBox target world.body.position.position := by
  rw [goalSatisfied_eq world _ installed]
  exact find_satisfied_iff _ _ _ _

/-! ## Absorbing goals -/

/-- The goals whose condition no world step can undo: a craft goal and a gold goal. -/
def Absorbing : Goal → Prop
  | .craft _ => True
  | .collect .gold _ => True
  | _ => False

/-- An absorbing goal whose condition the inventory meets. -/
def Kept : Goal → Inventory → Prop
  | .craft tool, inventory => inventory.owns tool = true
  | .collect .gold count, inventory => count.toNat ≤ inventory.gold.toNat
  | _, _ => False

/-- A kept goal stays kept across every write that retains tools and gold. -/
theorem kept_retained (goal : Goal) (before after : Inventory) (kept : Kept goal before)
    (retains : Retains before after) : Kept goal after := by
  cases goal with
  | craft tool =>
    cases tool with
    | axe => exact retains.axe kept
    | boat => exact retains.boat kept
  | collect item count =>
    cases item with
    | gold => exact Nat.le_trans kept retains.gold
    | wood => exact False.elim kept
    | stone => exact False.elim kept
    | food => exact False.elim kept
  | reach target => exact False.elim kept
  | survive steps => exact False.elim kept
  | find target => exact False.elim kept

/-- A world whose inventory keeps its installed goal reports the goal satisfied. -/
theorem kept_satisfied {config : WorldConfig} (world : World config) (goal : Goal)
    (installed : world.goal = some goal) (kept : Kept goal world.body.inventory) :
    world.goalSatisfied = true := by
  rw [goalSatisfied_eq world goal installed]
  cases goal with
  | craft tool => rw [craft_satisfied]; exact kept
  | collect item count =>
    cases item with
    | gold => exact (collect_satisfied_iff _ _ _ _ _).mpr kept
    | wood => exact False.elim kept
    | stone => exact False.elim kept
    | food => exact False.elim kept
  | reach target => exact False.elim kept
  | survive steps => exact False.elim kept
  | find target => exact False.elim kept

/-- An absorbing goal that a world reports satisfied is kept by its inventory. -/
theorem satisfied_kept {config : WorldConfig} (world : World config) (goal : Goal)
    (absorbing : Absorbing goal) (installed : world.goal = some goal)
    (achieved : world.goalSatisfied = true) : Kept goal world.body.inventory := by
  rw [goalSatisfied_eq world goal installed] at achieved
  cases goal with
  | craft tool => rw [craft_satisfied] at achieved; exact achieved
  | collect item count =>
    cases item with
    | gold => exact (collect_satisfied_iff _ _ _ _ _).mp achieved
    | wood => exact False.elim absorbing
    | stone => exact False.elim absorbing
    | food => exact False.elim absorbing
  | reach target => exact False.elim absorbing
  | survive steps => exact False.elim absorbing
  | find target => exact False.elim absorbing

/-- A goal the inventory already keeps is achieved by the first step of its attempt,
whatever the action. -/
theorem kept_first_step {config : WorldConfig} (world next : World config) (goal : Goal)
    (action : Action) (events : StepResult) (kept : Kept goal world.body.inventory)
    (h : (world.setGoal goal).step action = .ok (next, events)) : events.done = true := by
  rw [World.step_completion _ _ _ _ h]
  have installed : next.goal = some goal := (World.step_goal _ _ _ _ h).1
  exact kept_satisfied next goal installed
    (kept_retained goal _ _ kept (step_retains (world.setGoal goal) next action events h))

/-- A world reached from another by world steps and goal installations in any order:
what a campaign does to one persistent world between two visits to a goal. -/
inductive Later {config : WorldConfig} : World config → World config → Prop where
  /-- Nothing happened. -/
  | here (world : World config) : Later world world
  /-- One successful world step, whatever the action. -/
  | step {world next final : World config} {action : Action} {events : StepResult}
      (stepped : world.step action = .ok (next, events)) (rest : Later next final) :
      Later world final
  /-- One goal installation, which leaves the body as it is. -/
  | install {world final : World config} (goal : Goal) (rest : Later (world.setGoal goal) final) :
      Later world final

/-- No campaign removes an owned tool or lowers gold. -/
theorem later_retains {config : WorldConfig} {world final : World config}
    (later : Later world final) : Retains world.body.inventory final.body.inventory := by
  induction later with
  | here world => exact Retains.refl _
  | step stepped rest ih => exact (step_retains _ _ _ _ stepped).trans ih
  | install goal rest ih => exact ih

/-- A craft or gold goal achieved once is achieved at the first step of every later
visit, whatever either visit's actions and whatever was installed and done between
them. -/
theorem absorbing_revisit {config : WorldConfig} (world final next : World config) (goal : Goal)
    (absorbing : Absorbing goal) (installed : world.goal = some goal)
    (achieved : world.goalSatisfied = true) (later : Later world final) (action : Action)
    (events : StepResult) (h : (final.setGoal goal).step action = .ok (next, events)) :
    events.done = true :=
  kept_first_step final next goal action events
    (kept_retained goal _ _ (satisfied_kept world goal absorbing installed achieved)
      (later_retains later)) h

/-! ## Survive goals -/

/-- With a survive goal installed, a step's completion flag reads the successor's
saturating time since installation, and nothing about the action. -/
theorem survive_step {config : WorldConfig} (world next : World config) (action : Action)
    (events : StepResult) (required : UInt64) (h : world.step action = .ok (next, events))
    (installed : world.goal = some (.survive required)) :
    events.done = true ↔ required.toNat ≤ next.time.toNat - next.goalStart.toNat := by
  have after : next.goal = some (.survive required) :=
    (World.step_goal _ _ _ _ h).1.trans installed
  rw [World.step_completion _ _ _ _ h, goalSatisfied_eq next _ after, survive_satisfied_iff,
    show (next.time.toNat - next.goalStart.toNat).toUInt64 =
      UInt64.ofNat (next.time.toNat - next.goalStart.toNat) from rfl,
    UInt64.toNat_ofNat_of_lt' (show next.time.toNat - next.goalStart.toNat < 2 ^ 64 by
      have := next.time.toNat_lt; omega)]

/-- The survive goals are independent of the policy. From a goal's installation, every
action sequence whose steps the world accepts satisfies a survive goal exactly when its
length has reached the required duration, provided the 64-bit clock does not wrap. -/
theorem survive_actions {config : WorldConfig} (world final : World config) (required : UInt64)
    (actions : List Action)
    (h : (world.setGoal (.survive required)).advanceActions actions = .ok final)
    (room : world.time.toNat + actions.length < 2 ^ 64) :
    final.goalSatisfied = true ↔ required.toNat ≤ actions.length := by
  have clock := World.advanceActions_clock _ _ _ h
  obtain ⟨goal, origin⟩ := World.advanceActions_goal _ _ _ h
  change final.time = world.time + actions.length.toUInt64 at clock
  change final.goal = some (.survive required) at goal
  change final.goalStart = world.time at origin
  have length : actions.length.toUInt64.toNat = actions.length :=
    UInt64.toNat_ofNat_of_lt' (show actions.length < 2 ^ 64 by omega)
  have time : final.time.toNat = world.time.toNat + actions.length := by
    rw [clock, UInt64.toNat_add, length]
    exact Nat.mod_eq_of_lt room
  rw [goalSatisfied_eq final _ goal, survive_satisfied_iff, origin, time,
    show (world.time.toNat + actions.length - world.time.toNat).toUInt64 =
      UInt64.ofNat (world.time.toNat + actions.length - world.time.toNat) from rfl,
    UInt64.toNat_ofNat_of_lt'
      (show world.time.toNat + actions.length - world.time.toNat < 2 ^ 64 by omega)]
  omega

/-- An attempt whose clock reads its step count: the 64-bit clock has not wrapped
since the goal was installed. -/
def Clocked {config : WorldConfig} {α : Type} {goal : Goal} {cap : UInt64}
    (attempt : Attempt config α goal cap) : Prop :=
  attempt.run.world.time.toNat = attempt.run.world.goalStart.toNat + attempt.steps.val

/-- Goal installation starts the attempt's clock at its origin. -/
theorem start_clocked {config : WorldConfig} {α : Type} (run : RunState config α) (goal : Goal)
    (cap : UInt64) : Clocked (Attempt.start run goal cap) := by
  change run.world.time.toNat = run.world.time.toNat + 0
  rfl

/-- A tick that acts keeps the attempt's clock at its step count, for every agent
callback, while the clock has room for one more tick. -/
theorem tick_clocked {config : WorldConfig} {α β : Type} {goal : Goal} {cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext)
    (attempt next : Attempt config α goal cap) (frame : StepFrame β)
    (h : attempt.tick callbacks context = .ok (next, some frame)) (clocked : Clocked attempt)
    (room : attempt.run.world.time.toNat + 1 < 2 ^ 64) : Clocked next := by
  obtain ⟨-, -, stepped, count⟩ := CurrentRunner.tick_acted callbacks context attempt next frame h
  have clock := World.step_clock _ _ _ _ stepped
  have origin := (World.step_goal _ _ _ _ stepped).2
  have one : (1 : UInt64).toNat = 1 := rfl
  unfold Clocked at clocked ⊢
  rw [clock, origin, count, UInt64.toNat_add, one, Nat.mod_eq_of_lt room]
  omega

/-- The survive goals are independent of the agent. For every agent callback, a tick
that acts under a survive goal reports completion exactly when the attempt's step count
has reached the required duration. A tick acts only below the cap, so this is a per-tick
statement: it does not show that an attempt reaches that step count. -/
theorem survive_tick {config : WorldConfig} {α β : Type} {required cap : UInt64}
    (callbacks : AgentCallbacks order α β) (context : GoalContext)
    (attempt next : Attempt config α (.survive required) cap) (frame : StepFrame β)
    (h : attempt.tick callbacks context = .ok (next, some frame)) (clocked : Clocked attempt)
    (room : attempt.run.world.time.toNat + 1 < 2 ^ 64) :
    next.run.carried.events.done = true ↔ required.toNat ≤ next.steps.val := by
  obtain ⟨-, -, stepped, -⟩ := CurrentRunner.tick_acted callbacks context attempt next frame h
  have after := tick_clocked callbacks context attempt next frame h clocked room
  rw [survive_step _ _ _ _ required stepped attempt.installed]
  unfold Clocked at after
  omega

end AcornVerif.CurrentGoals
