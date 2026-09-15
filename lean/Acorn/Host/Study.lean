/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentAdmission
import AcornSpec.StudySchedule

/-!
# Current execution of the retained five-arm study schedules

These commands use the current full agent at the selected source revision.
They do not rerun the historical evaluator or claim to recreate old observations.
The opportunity loop installs a goal once per occurrence, carries the previous
result across attempts, records attempts but has no environment-accounting
callback, and discards a partial attempt when a diagnostic budget is exhausted.
This is the retained study schedule, distinct from the ordinary demo schedule.
No command is executed merely by compiling these definitions.
-/
namespace Acorn.Host.Study
open Features Handcrafted

/-- The four schedules sharing the original five-arm opportunity loop. -/
inductive Kind where
  /-- Foundation comparison. -/
  | baseline
  /-- Primitive intra-option credit. -/
  | intraOption
  /-- Per-learner exploration rates. -/
  | exploration
  /-- Learned subtask selection. -/
  | planning
  deriving DecidableEq

/-- An arm is exactly one position in the owning study's closed five-arm schema. -/
abbrev Arm := Fin 5

/-- Canonical dossier slug. -/
def Kind.slug : Kind → String
  | .baseline => "agent-baseline" | .intraOption => "intra-option-credit"
  | .exploration => "derived-exploration-rate" | .planning => "stomp-planning"

/-- Stable arm spellings follow the retained protocol order. -/
def Kind.arms : Kind → Vector String 5
  | .baseline => #v["final", "random", "frozen", "ablated_goal_relation", "ablated_temporal_abstraction"]
  | .intraOption => #v["final", "random", "frozen", "ablated_intra_option", "ablated_span_credit"]
  | .exploration => #v["final", "random", "frozen", "ablated_annealed_schedule", "ablated_shared_rate"]
  | .planning => #v["final", "random", "frozen", "ablated_hand_authored_subtasks", "ablated_temporal_abstraction"]

/-- Arm admission searches only the schema's finite domain. -/
def Kind.arm (kind : Kind) (name : String) : Option Arm :=
  (List.finRange 5).find? fun index => kind.arms.get index == name

/-- The scientific initialization domain is separate from each world seed. -/
def Kind.agentSeed : Kind → UInt64
  | .baseline => AcornSpec.Constants.agentSeedValue
  | .intraOption => AcornSpec.Constants.Compatibility.Domain.intraOptionCreditInitialization.value
  | .exploration => AcornSpec.Constants.Compatibility.Domain.derivedExplorationRateInitialization.value
  | .planning => AcornSpec.Constants.Compatibility.Domain.stompPlanningInitialization.value

/-- The comparator stream retains the owning protocol's sealed domain. -/
def Kind.randomDomain : Kind → UInt64
  | .baseline => AcornSpec.Constants.Compatibility.Domain.agentBaselineRandom.value
  | .intraOption => AcornSpec.Constants.Compatibility.Domain.intraOptionCreditRandom.value
  | .exploration => AcornSpec.Constants.Compatibility.Domain.derivedExplorationRateRandom.value
  | .planning => AcornSpec.Constants.Compatibility.Domain.stompPlanningRandom.value

/-- Retained populations are the protocol's exact raw generator prefixes.
The baseline retains its sealed ordered literals. No fresh population is selected. -/
def Kind.seeds (kind : Kind) : Array UInt64 :=
  match kind with
  | .baseline => AcornSpec.Constants.heldOutSeeds
  | .intraOption | .exploration | .planning =>
    let domain := match kind with
      | .intraOption => AcornSpec.Constants.Compatibility.Domain.intraOptionCreditPopulation.value
      | .exploration => AcornSpec.Constants.Compatibility.Domain.derivedExplorationRatePopulation.value
      | .planning => AcornSpec.Constants.Compatibility.Domain.stompPlanningPopulation.value
      | .baseline => 0
    (Rng.runPrefix 30 (Rng.Xoshiro256.seed (Rng.streamKey domain 1))).1.toArray

/-- Current immutable discriminator choices for every protocol arm. -/
def Kind.profile (kind : Kind) (arm : Arm) : FeatureProfile :=
  let mode := if arm.val = 2 then EvaluationMode.frozen
    else if kind = .baseline && arm.val = 3 then .withoutReachRelation
    else if (kind = .baseline || kind = .planning) && arm.val = 4 then .primitiveOnly else .final
  let credit := if kind = .intraOption && arm.val = 3 then ControlCredit.smdpCatchUp
    else if kind = .intraOption && arm.val = 4 then .noSpanCredit else .perStep
  let rate := if kind = .exploration && arm.val = 3 then RatePolicy.annealed
    else if kind = .exploration && arm.val = 4 then .shared else .perLearner
  let subtasks := if kind = .planning && arm.val != 3 then SubtaskPolicy.learned else .spatial
  ⟨mode, credit, rate, subtasks⟩

/-- All agent-backed arms use the full ordinary dimension and scalar planner. -/
def Kind.construction (kind : Kind) (arm : Arm) : AgentConstruction :=
  { AgentConstruction.standard kind.agentSeed ⟨.ranked, .discounted⟩ .scalar with
    profile := kind.profile arm }

/-- The comparator has no agent state; the agent alternative is legal by its type. -/
inductive Policy (construction : AgentConstruction) where
  /-- Actual current composed learner. -/
  | agent (state : construction.State)
  /-- Separate pseudorandom stream. -/
  | random (stream : Rng.Xoshiro256)

/-- Random construction cannot allocate or initialize an unused learner. -/
def Kind.initial (kind : Kind) (arm : Arm) : Policy (kind.construction arm) :=
  if arm.val = 1 then .random (Rng.Xoshiro256.seed (Rng.streamKey kind.agentSeed kind.randomDomain))
  else .agent (kind.construction arm).initial

/-- Action selection uses the actual agent operation or a closed primitive draw. -/
def Policy.act {construction : AgentConstruction} {config : WorldConfig}
    (policy : Policy construction) (world : World config) (carried : RawStepResult) :
    Except WorldError (Action × Policy construction) := do
  match policy with
  | .agent state =>
    let observation ← world.observe
    let (action, next) := Agent.callbacks.act state observation carried
    return (action, .agent next)
  | .random stream =>
    let (index, next) := stream.nextBelow ⟨9, by decide⟩
    return (Action.fromIndex index.val.toNat, .random next)

/-- The comparator result is independent of both external observations and rewards. -/
theorem Policy.random_independent (construction : AgentConstruction) (stream : Rng.Xoshiro256)
    {config : WorldConfig} (left right : World config) (a b : RawStepResult) :
    (Policy.random (construction := construction) stream).act left a =
      (Policy.random stream).act right b := rfl

/-- Only agent-backed policies account for attempts; knowledge continues across them. -/
def Policy.attempt {construction : AgentConstruction} (policy : Policy construction)
    (family : GoalFamily) (cycle steps : UInt64) (achieved : Bool) : Policy construction :=
  match policy with
  | .random stream => .random stream
  | .agent state => .agent (state.recordAttempt (familyIndex family) cycle steps achieved)

/-- One retained attempt row, with the actual installed goal and raw reward. -/
structure Row where
  /-- Zero-based cycle. -/
  cycle : UInt64
  /-- Zero-based goal index. -/
  goalIndex : Fin AcornSpec.studyGoals
  /-- Actual installed goal. -/
  goal : Goal
  /-- Difficulty tier from the same curriculum. -/
  tier : UInt8
  /-- Zero-based attempt. -/
  attempt : Fin AcornSpec.attemptsPerGoal
  /-- Satisfied at goal installation, before the first attempt. -/
  initiallySatisfied : Bool
  /-- Bounded actions in this attempt. -/
  steps : Fin (AcornSpec.stepsPerAttempt.toNat + 1)
  /-- Terminal result after the final action. -/
  achieved : Bool
  /-- Ordered binary32 sum of actual rewards. -/
  reward : Binary32

/-- Every write carries the diagnostic budget and per-attempt cap. -/
structure State (world : WorldConfig) (construction : AgentConstruction) (budget : UInt64) where
  /-- World and current goal clock are never reset at an attempt boundary. -/
  world : World world
  /-- Actual continuing policy. -/
  policy : Policy construction
  /-- The previous environment result. -/
  carried : RawStepResult := {}
  /-- Binding action fold. -/
  fold : UInt64 := AcornSpec.Constants.foldInitValue
  /-- Total executed actions cannot exceed the supplied diagnostic budget. -/
  total : Fin (budget.toNat + 1) := ⟨0, by omega⟩
  /-- Current attempt action count. -/
  used : Fin (AcornSpec.stepsPerAttempt.toNat + 1) := ⟨0, by decide⟩
  /-- Current attempt reward sum. -/
  reward : Binary32 := .zero

/-- A single guarded step uses the owning world and agent definitions.
None means the budget or attempt cap is exhausted, before either state changes. -/
def State.tick {world : WorldConfig} {construction : AgentConstruction} {budget : UInt64}
    (state : State world construction budget) : Except WorldError (Option (Action × State world construction budget)) := do
  if ht : state.total.val < budget.toNat then
    if hu : state.used.val < AcornSpec.stepsPerAttempt.toNat then
      let (action, policy) ← state.policy.act state.world state.carried
      let (world, result) ← state.world.step action
      return some (action, { state with
        world := world, policy := policy, carried := result.raw,
        fold := foldAction state.fold action, total := ⟨state.total.val + 1, by omega⟩,
        used := ⟨state.used.val + 1, by omega⟩, reward := state.reward.add result.reward })
    else return none
  else return none

/-- The diagnostic budget refuses before action selection or environment execution. -/
theorem State.exhausted {world : WorldConfig} {construction : AgentConstruction} {budget : UInt64}
    (state : State world construction budget) (spent : state.total.val = budget.toNat) :
    state.tick = .ok none := by simp [tick, spent, pure, Except.pure]

/-- Run the finite retained opportunity schedule with one-way action diagnostics.
No rows from an interrupted attempt are represented as complete observations. -/
def run (kind : Kind) (arm : Arm) (seed budget : UInt64)
    (onAction : UInt64 → Action → IO Unit) : IO (Except String (Array Row × UInt64)) := do
  let .ok config := WorldConfig.standard seed ⟨AcornSpec.studyWorldSide, by decide⟩
    | return .error "study world configuration refused"
  let .ok world := World.initial config | return .error "study world initialization refused"
  let mut state : State config (kind.construction arm) budget := { world := world, policy := kind.initial arm }
  let mut rows := #[]
  for cycle in [:AcornSpec.studyCycles] do
    for goalIndex in List.finRange AcornSpec.studyGoals do
      let (goal, tier) := standardCurriculumEntry config.raw.side seed goalIndex.val.toUInt64
      state := { state with world := state.world.setGoal goal }
      let initially := state.world.goalSatisfied
      for attempt in List.finRange AcornSpec.attemptsPerGoal do
        state := { state with used := ⟨0, by decide⟩, reward := .zero }
        for _ in [:AcornSpec.stepsPerAttempt.toNat] do
          match state.tick with
          | .error _ => return .error "study world transition refused"
          | .ok none => return .ok (rows, state.fold)
          | .ok (some (action, next)) =>
            onAction state.total.val.toUInt64 action
            state := next
            if state.carried.events.done then break
        state := { state with policy := state.policy.attempt goal.family cycle.toUInt64 state.used.val.toUInt64 state.carried.events.done }
        rows := rows.push ⟨cycle.toUInt64, goalIndex, goal, tier, attempt, initially,
          state.used, state.carried.events.done, state.reward⟩
        if state.carried.events.done then break
  return .ok (rows, state.fold)

end Acorn.Host.Study
