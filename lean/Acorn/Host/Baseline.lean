import Acorn.Host.Runner

namespace Acorn.Host

def baselineActionCount : Word.Count := ⟨FeatureConstants.primitiveCount.toUInt64, by decide⟩

def baselineAction (rng : Rng.Xoshiro256) : Action × Rng.Xoshiro256 :=
  let draw := rng.nextBelow baselineActionCount
  (Action.fromIndex draw.1.val.toNat, draw.2)

def baselineStream (seed : UInt64) : Rng.Xoshiro256 :=
  Rng.Xoshiro256.seed (Rng.streamKey seed 0xba5e000000000001)

structure BaselineAttempt (config : WorldConfig) (cap : UInt64) where
  world : World config
  rng : Rng.Xoshiro256
  steps : Fin (cap.toNat + 1)
  result : StepResult

def BaselineAttempt.start {config : WorldConfig} (world : World config) (rng : Rng.Xoshiro256)
    (goal : Goal) (cap : UInt64) : BaselineAttempt config cap :=
  ⟨world.setGoal goal, rng, ⟨0, by omega⟩, {}⟩

def BaselineAttempt.tick {config : WorldConfig} {cap : UInt64} (state : BaselineAttempt config cap) :
    Except WorldError (BaselineAttempt config cap) :=
  if state.result.done then .ok state
  else if hs : state.steps.val < cap.toNat then
    let drawn := baselineAction state.rng
    match state.world.step drawn.1 with
    | .error error => .error error
    | .ok (world, result) => .ok ⟨world, drawn.2, ⟨state.steps.val + 1, by omega⟩, result⟩
  else .ok state

def BaselineAttempt.run {config : WorldConfig} {cap : UInt64} :
    Nat → BaselineAttempt config cap → Except WorldError (BaselineAttempt config cap)
  | 0, state => .ok state
  | fuel + 1, state =>
    match state.tick with
    | .error error => .error error
    | .ok next => if next.result.done then .ok next else BaselineAttempt.run fuel next

structure BaselineOutcome where
  context : GoalContext
  steps : UInt64
  achieved : Bool
  position : Position

def BaselineAttempt.outcome {config : WorldConfig} {cap : UInt64}
    (state : BaselineAttempt config cap) (context : GoalContext) : BaselineOutcome :=
  ⟨context, state.steps.val.toUInt64, state.result.done, state.world.body.position.position⟩

inductive BaselineError where
  | campaign (error : CampaignError)
  | world (error : WorldError)
  | unfinished

def CampaignPlan.attemptBudget {size : Nat} (plan : CampaignPlan size) : Nat :=
  plan.cycles.toNat * plan.goals.val * plan.attempts.toNat

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
