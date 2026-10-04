/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Runner

/-!
# Random-policy comparator

This is the explicitly requested demo comparison, not an agent callback or
substitute for the learned composition. It follows the campaign the agent
follows: the same admitted plan, curriculum lookup, goal installation, step cap
and attempt-boundary function, in a second copy of the initial world that it
carries from attempt to attempt. Its actions come from its own seeded stream and
from nothing else. Each row reports where in the campaign its attempt was made,
its steps, its completion flag and the body position at its end. An unbounded
campaign has no completing boundary and so no complete record; it is refused.
-/
namespace Acorn.Host

/-- The receiving range of one comparator draw: the nine primitive actions. -/
def baselineActionCount : Word.Count := ⟨FeatureConstants.primitiveCount.toUInt64, by decide⟩

/-- One comparator action and the advanced stream. The stream is the only
argument, so no world, observation, goal or result can enter the choice. -/
def baselineAction (rng : Rng.Xoshiro256) : Action × Rng.Xoshiro256 :=
  let draw := rng.nextBelow baselineActionCount
  (Action.fromIndex draw.1.val.toNat, draw.2)

/-- The comparator's own stream of the run's seed. -/
def baselineStream (seed : UInt64) : Rng.Xoshiro256 :=
  Rng.Xoshiro256.seed (Rng.streamKey seed 0xba5e000000000001)

/-- A comparator attempt carries its cap at each state write. -/
structure BaselineAttempt (config : WorldConfig) (cap : UInt64) where
  /-- Current environment. -/
  world : World config
  /-- Separate diagnostic action stream. -/
  rng : Rng.Xoshiro256
  /-- Bounded action count. -/
  steps : Fin (cap.toNat + 1)
  /-- Result of this attempt's last world step, initially empty. -/
  result : StepResult

/-- Goal installation starts an attempt with no step taken and an empty result,
so a completion carried from an earlier attempt cannot end this one. -/
def BaselineAttempt.start {config : WorldConfig} (world : World config) (rng : Rng.Xoshiro256)
    (goal : Goal) (cap : UInt64) : BaselineAttempt config cap :=
  ⟨world.setGoal goal, rng, ⟨0, by omega⟩, {}⟩

/-- One drawn action and world transition, until the goal is satisfied or the cap is reached. -/
def BaselineAttempt.tick {config : WorldConfig} {cap : UInt64} (state : BaselineAttempt config cap) :
    Except WorldError (BaselineAttempt config cap) :=
  if state.result.done then .ok state
  else if hs : state.steps.val < cap.toNat then
    let drawn := baselineAction state.rng
    match state.world.step drawn.1 with
    | .error error => .error error
    | .ok (world, result) => .ok ⟨world, drawn.2, ⟨state.steps.val + 1, by omega⟩, result⟩
  else .ok state

/-- Tick until the goal is satisfied or the fuel is spent. With the cap as fuel
this is a whole attempt, because a tick at the cap takes no step. -/
def BaselineAttempt.run {config : WorldConfig} {cap : UInt64} :
    Nat → BaselineAttempt config cap → Except WorldError (BaselineAttempt config cap)
  | 0, state => .ok state
  | fuel + 1, state =>
    match state.tick with
    | .error error => .error error
    | .ok next => if next.result.done then .ok next else BaselineAttempt.run fuel next

/-- One comparator attempt: where in the campaign it was made and how it ended.
The comparator has no learner, so the row has no learner observation. -/
structure BaselineOutcome where
  /-- Goal index, attempt number, tier and cycle of the attempt. -/
  context : GoalContext
  /-- Number of actions executed in the attempt. -/
  steps : UInt64
  /-- Completion flag after the attempt's last world step. -/
  achieved : Bool
  /-- Body position after the attempt's last world step. -/
  position : Position

/-- The row of an attempt reads that attempt's own final state. -/
def BaselineAttempt.outcome {config : WorldConfig} {cap : UInt64}
    (state : BaselineAttempt config cap) (context : GoalContext) : BaselineOutcome :=
  ⟨context, state.steps.val.toUInt64, state.result.done, state.world.body.position.position⟩

/-- Why the comparator returned no record. -/
inductive BaselineError where
  /-- Campaign admission refused the schedule, as it refuses the agent's. -/
  | campaign (error : CampaignError)
  /-- World generation or a world transition refused. -/
  | world (error : WorldError)
  /-- The campaign did not reach its completing boundary within its attempt budget. -/
  | unfinished

/-- The most attempts a campaign can make: every cycle visits every goal for
every attempt. It is zero for an unbounded campaign. -/
def CampaignPlan.attemptBudget {size : Nat} (plan : CampaignPlan size) : Nat :=
  plan.cycles.toNat * plan.goals.val * plan.attempts.toNat

/-- The comparator's campaign from a live cursor. Each pass installs the cursor's
goal, runs one attempt, records it and asks the agent's own boundary function,
with no stop request, what follows. A truncated campaign is never returned as a
record: spent fuel and a stopped boundary are both refusals. -/
def runBaselineCampaign {config : WorldConfig} (curriculum : Curriculum)
    (plan : CampaignPlan curriculum.size) :
    Nat → CampaignCursor plan → World config → Rng.Xoshiro256 → Array BaselineOutcome →
      Except BaselineError (Array BaselineOutcome)
  | 0, _, _, _, _ => .error .unfinished
  | fuel + 1, cursor, world, rng, outcomes =>
    have hg : cursor.goal.val < curriculum.size := by
      have := cursor.goal.isLt; have := plan.goals.isLt; omega
    let entry := curriculum[cursor.goal.val]'hg
    match BaselineAttempt.run plan.stepCap.toNat
        (BaselineAttempt.start world rng entry.1 plan.stepCap) with
    | .error error => .error (.world error)
    | .ok state =>
      let outcomes := outcomes.push (state.outcome (cursor.context entry.2))
      match atAttemptBoundary cursor state.result.done false with
      | .continue next =>
        runBaselineCampaign curriculum plan fuel next state.world state.rng outcomes
      | .complete => .ok outcomes
      | .stopped => .error .unfinished

/-- Complete public diagnostic over the campaign the agent's runner admits from
the same arguments: the standard curriculum of the world and seed, the admitted
plan and one initial world, with explicit refusal. One row per attempt is
returned, in campaign order. -/
def runRandomBaseline (config : WorldConfig) (seed : UInt64) (spec : CampaignSpec) :
    Except BaselineError (Array BaselineOutcome) :=
  let curriculum := standardCurriculum config seed
  match CampaignPlan.admit curriculum.size spec with
  | .error error => .error (.campaign error)
  | .ok plan =>
    match World.initial config with
    | .error error => .error (.world error)
    | .ok world =>
      match plan.initial with
      | .continue cursor =>
        runBaselineCampaign curriculum plan plan.attemptBudget cursor world (baselineStream seed)
          #[]
      | .complete => .ok #[]
      | .stopped => .error .unfinished

end Acorn.Host
