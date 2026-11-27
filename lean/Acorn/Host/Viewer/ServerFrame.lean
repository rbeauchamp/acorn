import Acorn.Host.Viewer.BrowserStore
import Acorn.Host.Viewer.BrowserNat
import Acorn.Host.Viewer.ClockProgram
import Acorn.Host.Viewer.DecimalText
import Acorn.Host.Viewer.IdentityHandshake
import Acorn.Host.Viewer.Sensed
import Acorn.Host.Viewer.Wire

namespace Acorn.Host.Viewer

open DecimalText

structure GoalProgressSnapshot where
  goalCount : Nat
  attemptCap : Nat
  stepCap : Nat
  invalid : Bool
  cycle : Nat
  resolved : Nat
  attempt : Nat
  achieved : Nat
  completedCycle : Option Nat
  completedAchieved : Option Nat
  score : Option Nat
  curriculumNames : Array String
  curriculumFailed : Array Nat
  curriculumSuccessSteps : Array (Option Nat)
  activeGoal : Nat

structure AgreementSnapshot where
  sourceSha : String
  buildSha : String
  processStartedMs : Nat
  clock : Nat
  scale : Nat
  started : Option Nat
  stopped : Bool
  score : Option Nat
  text : Option String
  error : Option Nat
  channelScore : Array (Option Nat)
  channelText : Array (Option String)
  channelError : Array (Option Nat)
  count : Array String
  pending : Array Nat
  censored : Array String
  status : Array String
  horizon : Array Nat
  startFirst : Array (Option Nat)
  startLast : Array (Option Nat)
  settlementFirst : Array (Option Nat)
  settlementLast : Array (Option Nat)
  tail : Array (Option Nat)
  rounding : Array (Option Nat)
  historyClock : Array (Option Nat)
  historyScore : Array (Option Nat)
  settleStride : Nat
  demonNames : Array String
  demonTargetPolicy : Array String
  demonGamma : Array Scalar
  demonHorizon : Array Scalar
  goalProgress : GoalProgressSnapshot

structure FrameSummary where
  runId : String
  agentEpoch : Nat
  origin : String
  timestampMs : Nat
  worldStep : Nat
  lifetimeStep : Nat
  side : Nat
  dayLength : Nat
  x : Int
  y : Int
  facing : Nat
  action : Nat
  reward : Scalar
  done : Bool
  terminal : Bool
  goal : Nat
  cycle : Nat
  decisionSource : String
  skill : Nat
  explored : Bool
  optionStart : Nat
  optionEndSkill : Nat
  optionEndReason : Nat
  eps : Scalar
  updateUs : Nat
  environmentUs : Nat
  aCtl : Scalar
  aDem : Scalar
  aMeta : Option Decimal
  aOpt : Option Decimal
  nonFiniteKey : Option String

structure ServerFrame where
  summary : FrameSummary
  sourceSha : String
  buildSha : String
  auditDigest : String
  seed : Nat
  energy : Nat
  wood : Nat
  stone : Nat
  food : Nat
  gold : Nat
  axe : Bool
  boat : Bool
  ev : Nat
  attempt : Nat
  tier : Nat
  gkind : Nat
  gitem : Nat
  gx : Int
  gy : Int
  gn : Nat
  tiles : Array Nat
  tileExtra : Array Nat
  rewardRate : Scalar
  controlCriterion : Nat
  processUptimeMs : Nat
  coreRssBytes : Option Nat
  checkpointBytes : Option Nat
  checkpointWriteUs : Option Nat
  checkpointFailures : Nat
  telemetryRefusals : Nat
  telemetryDrops : Nat
  weightSpace : Nat
  nTilings : Nat
  imprintUnits : Nat
  retireStep : Option Nat
  retireUnit : Option Nat
  retireCount : Nat
  subtaskPolicy : String
  subtaskUnit : Array (Option Nat)
  subtaskBonus : Array Scalar
  actionNames : Array String
  metaNames : Array String
  skillNames : Array String
  goalFamilyNames : Array String
  controlValues : Array Scalar
  metaValues : Array Scalar
  actionProbs : Array Scalar
  metaProbs : Array Scalar
  metaAction : Nat
  optionElapsed : Nat
  optionEndDuration : Nat
  optionModelRewards : Array Scalar
  optionModelContinuations : Array Scalar
  optionModelDurations : Array Scalar
  planningSteps : Nat
  planningErrors : Array Scalar
  alphaControl : Array Scalar
  alphaMeta : Array Scalar
  alphaOptions : Array Scalar
  alphaDemons : Array Scalar
  alphaModels : Array Scalar
  creditControl : Array Nat
  creditMeta : Array Nat
  creditOptions : Array Nat
  creditDemons : Array Nat
  creditModels : Array Nat
  demons : Array Scalar
  cums : Array Scalar
  settledReturn : Array Scalar
  settledError : Array Scalar
  lifetimeRewardSum : Scalar
  lifetimeRewardCount : Nat
  lifetimeRewardHistorySum : Array Scalar
  lifetimeRewardHistoryCount : Array Nat
  lifetimeErrorHistorySum : Array Scalar
  lifetimeErrorHistoryCount : Array Nat
  lifetimeOptionStarted : Array Nat
  lifetimeOptionCompleted : Array Nat
  lifetimeOptionDuration : Array Nat
  lifetimeOptionEndReasons : Array Nat
  lifetimeGoalAttempts : Array Nat
  lifetimeGoalSuccesses : Array Nat
  lifetimeGoalSteps : Array Nat
  lifetimeCycleAttempts : Array Nat
  lifetimeCycleSuccesses : Array Nat
  lifetimeCycleSteps : Array Nat
  agreement : AgreementSnapshot

structure HistorySample where
  aDem : Option Decimal
  aCtl : Option Decimal
  aMeta : Option Decimal
  aOpt : Option Decimal
  surprise : Option Decimal

structure RefusalRecord where
  reason : BrowserRefusal
  key : String

def historySampleCapacity : Nat := 400

def verifyStride : Nat := 24

structure CaptureRate where
  bucketSec : Nat := 0
  currentCount : Nat := 0
  previousCount : Nat := 0
  hasBucket : Bool := false
  hasPrevious : Bool := false
  firstMonoMs : Nat := 0
  deriving DecidableEq, BEq

def CaptureRate.record (r : CaptureRate) (nowMonoMs : Nat) : CaptureRate :=
  let sec := nowMonoMs / 1000
  if !r.hasBucket then
    { bucketSec := sec
      currentCount := 1
      previousCount := 0
      hasBucket := true
      hasPrevious := false
      firstMonoMs := nowMonoMs }
  else if sec == r.bucketSec then
    { r with currentCount := r.currentCount + 1 }
  else if sec == r.bucketSec + 1 then
    { r with
      bucketSec := sec
      currentCount := 1
      previousCount := r.currentCount
      hasPrevious := true }
  else if sec > r.bucketSec + 1 then
    { r with
      bucketSec := sec
      currentCount := 1
      previousCount := 0
      hasPrevious := true }
  else
    { r with currentCount := r.currentCount + 1 }

def CaptureRate.framesPerSecondTenths (r : CaptureRate) (nowMonoMs : Nat) : Option Nat :=
  if !r.hasBucket then none
  else
    let nowSec := nowMonoMs / 1000
    let elapsedInSec := nowMonoMs % 1000
    if nowSec == r.bucketSec then
      if r.hasPrevious then
        some ((r.previousCount + r.currentCount) * 10000 / (1000 + elapsedInSec))
      else
        let spanMs := nowMonoMs - r.firstMonoMs
        if r.currentCount < 2 || spanMs < 250 then none
        else some ((r.currentCount - 1) * 10000 / spanMs)
    else if nowSec == r.bucketSec + 1 then
      some (r.currentCount * 10000 / (1000 + elapsedInSec))
    else if nowSec > r.bucketSec + 1 then
      some 0
    else
      none

inductive StreamLiveness where
  | idle
  | busy (label : String)
  | waitingForCapture
  | stale (hasCapture : Bool)
  | live
  | fault (exhausted : Bool)
  deriving DecidableEq, BEq

structure ServerObserverState where
  identity : Identity
  admission : Admission identity
  healthAdmission : HealthAdmission identity
  summaries : Buffer FrameSummary replayCapacity := .empty
  latest : Option ServerFrame := none
  agreement : Option AgreementSnapshot := none
  samples : Buffer HistorySample historySampleCapacity := .empty
  admittedCount : Nat := 0
  refusedCount : Nat := 0
  lastRefusal : Option RefusalRecord := none
  nonFiniteCount : Nat := 0
  lastNonFiniteKey : Option String := none
  lastFreshMonoMs : Option Nat := none
  lastFreshOrigin : Option String := none
  captureRate : CaptureRate := {}
  lastRetireCount : Option Nat := none
  retireChangedAt : Option Nat := none
  lastSubtaskSig : Option String := none
  subtaskChangedAt : Option Nat := none
  lastPlanningSteps : Option Nat := none
  planningChangedAt : Option Nat := none
  prevDemons : Option (Nat × Array Scalar) := none

def ServerObserverState.empty (identity : Identity) : ServerObserverState where
  identity := identity
  admission := .empty identity
  healthAdmission := .empty identity

private def fieldOf (fields : List (String × Json.Value)) (key : String) :
    Except (BrowserRefusal × String) Json.Value :=
  match fields.find? (fun p => p.1 == key) with
  | some (_, v) => .ok v
  | none => .error (.missingField, key)

private def isLowerHex (width : Nat) (s : String) : Bool :=
  s.length == width && s.toList.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

private def isDecimalUpTo (maximum : Nat) (s : String) : Bool :=
  match Digits.read s with
  | some n =>
    (s == "0" || !s.startsWith "0") && n ≤ maximum
  | none => false

private def reqNat (fields : List (String × Json.Value)) (key : String) :
    Except (BrowserRefusal × String) Nat := do
  let v ← fieldOf fields key
  match v.natural with
  | .ok n =>
    if n ≤ browserIntegerMax then return n else throw (.malformed, key)
  | .error _ => throw (.malformed, key)

private def reqOptNat (fields : List (String × Json.Value)) (key : String) :
    Except (BrowserRefusal × String) (Option Nat) := do
  match ← fieldOf fields key with
  | .null => return none
  | v =>
    match v.natural with
    | .ok n =>
      if n ≤ browserIntegerMax then return some n else throw (.malformed, key)
    | .error _ => throw (.malformed, key)

private def reqInt (fields : List (String × Json.Value)) (key : String) :
    Except (BrowserRefusal × String) Int := do
  match ← fieldOf fields key with
  | .number s =>
    match Digits.integer s with
    | some n =>
      if n.natAbs ≤ browserIntegerMax then return n else throw (.malformed, key)
    | none => throw (.malformed, key)
  | _ => throw (.malformed, key)

private def reqBool (fields : List (String × Json.Value)) (key : String) :
    Except (BrowserRefusal × String) Bool := do
  match ← fieldOf fields key with
  | .bool b => return b
  | _ => throw (.malformed, key)

private def reqStr (fields : List (String × Json.Value)) (key : String) :
    Except (BrowserRefusal × String) String := do
  match ← fieldOf fields key with
  | .string s => return s
  | _ => throw (.malformed, key)

private def reqOptStr (fields : List (String × Json.Value)) (key : String) :
    Except (BrowserRefusal × String) (Option String) := do
  match ← fieldOf fields key with
  | .null => return none
  | .string s => return some s
  | _ => throw (.malformed, key)

private def reqScalar (fields : List (String × Json.Value)) (key : String) :
    Except (BrowserRefusal × String) Scalar := do
  match Scalar.fromJson (← fieldOf fields key) with
  | .ok s => return s
  | .error _ => throw (.malformed, key)

private def reqList (fields : List (String × Json.Value)) (key : String) (expected : Option Nat) :
    Except (BrowserRefusal × String) (List Json.Value) := do
  match ← fieldOf fields key with
  | .array xs =>
    match expected with
    | some n => if xs.length == n then return xs else throw (.cardinality, key)
    | none => return xs
  | _ => throw (.malformed, key)

private def reqNatArr (fields : List (String × Json.Value)) (key : String) (expected : Option Nat) :
    Except (BrowserRefusal × String) (Array Nat) := do
  let xs ← reqList fields key expected
  let mut out := #[]
  for v in xs do
    match v.natural with
    | .ok n =>
      if n ≤ browserIntegerMax then out := out.push n else throw (.malformed, key)
    | .error _ => throw (.malformed, key)
  return out

private def reqOptNatArr (fields : List (String × Json.Value)) (key : String)
    (expected : Option Nat) : Except (BrowserRefusal × String) (Array (Option Nat)) := do
  let xs ← reqList fields key expected
  let mut out := #[]
  for v in xs do
    match v with
    | .null => out := out.push none
    | _ =>
      match v.natural with
      | .ok n =>
        if n ≤ browserIntegerMax then out := out.push (some n) else throw (.malformed, key)
      | .error _ => throw (.malformed, key)
  return out

private def reqStrArr (fields : List (String × Json.Value)) (key : String) (expected : Option Nat) :
    Except (BrowserRefusal × String) (Array String) := do
  let xs ← reqList fields key expected
  let mut out := #[]
  for v in xs do
    match v with
    | .string s => out := out.push s
    | _ => throw (.malformed, key)
  return out

private def reqOptStrArr (fields : List (String × Json.Value)) (key : String)
    (expected : Option Nat) : Except (BrowserRefusal × String) (Array (Option String)) := do
  let xs ← reqList fields key expected
  let mut out := #[]
  for v in xs do
    match v with
    | .null => out := out.push none
    | .string s => out := out.push (some s)
    | _ => throw (.malformed, key)
  return out

private def reqScalarArr (fields : List (String × Json.Value)) (key : String)
    (expected : Option Nat) : Except (BrowserRefusal × String) (Array Scalar) := do
  let xs ← reqList fields key expected
  let mut out := #[]
  for v in xs do
    match Scalar.fromJson v with
    | .ok s => out := out.push s
    | .error _ => throw (.malformed, key)
  return out

private def checkExact (key : String) (actual expected : Nat)
    (why : BrowserRefusal := .cardinality) : Except (BrowserRefusal × String) Unit :=
  if actual == expected then .ok () else .error (why, key)

private def checkBound (key : String) (ok : Bool) : Except (BrowserRefusal × String) Unit :=
  if ok then .ok () else .error (.malformed, key)

private def firstNonFinite (checks : List (String × Bool)) : Option String :=
  (checks.find? fun (_, finite) => !finite).map Prod.fst

private def allFinite (xs : Array Scalar) : Bool :=
  xs.all Scalar.isFinite

def decodeServerFrame (value : Json.Value) : Except (BrowserRefusal × String) ServerFrame := do
  let fields ← match value with
    | .object fs => pure fs
    | _ => throw (.malformed, "frame")
  for (key, _) in browserSchema do
    let _ ← fieldOf fields key
  let schemaVer ← reqNat fields "schema_version"
  checkExact "schema_version" schemaVer telemetrySchemaVersion .schema
  let sourceSha ← reqStr fields "source_sha256"
  checkBound "source_sha256" (isLowerHex 64 sourceSha)
  let buildSha ← reqStr fields "build_sha256"
  checkBound "build_sha256" (isLowerHex 64 buildSha)
  let auditDigest ← reqStr fields "audit_digest"
  checkBound "audit_digest" (isLowerHex 16 auditDigest)
  let runId ← reqStr fields "run_id"
  checkBound "run_id" (isLowerHex 16 runId)
  let agentEpoch ← reqNat fields "agent_epoch"
  let origin ← reqStr fields "origin"
  checkBound "origin" (["fresh", "resumed", "cleared"].contains origin)
  let timestampMs ← reqNat fields "timestamp_ms"
  let updateUs ← reqNat fields "update_us"
  let environmentUs ← reqNat fields "environment_us"
  let processUptimeMs ← reqNat fields "process_uptime_ms"
  let processStartedMs ← reqNat fields "process_started_ms"
  let coreRssBytes ← reqOptNat fields "core_rss_bytes"
  let checkpointBytes ← reqOptNat fields "checkpoint_bytes"
  let checkpointWriteUs ← reqOptNat fields "checkpoint_write_us"
  let checkpointFailures ← reqNat fields "checkpoint_failures"
  let telemetryRefusals ← reqNat fields "telemetry_refusals"
  let telemetryDrops ← reqNat fields "telemetry_drops"
  let goalCount ← reqNat fields "goal_count"
  let attemptCap ← reqNat fields "attempt_cap"
  let stepCap ← reqNat fields "step_cap"
  let _cycleCap ← reqNat fields "cycle_cap"
  let gpInvalid ← reqBool fields "goal_progress_invalid"
  let gpCycle ← reqNat fields "goal_progress_cycle"
  let gpResolved ← reqNat fields "goal_progress_resolved"
  let gpAttempt ← reqNat fields "goal_progress_attempt"
  let gpAchieved ← reqNat fields "goal_progress_achieved"
  let gpCompCycle ← reqOptNat fields "goal_progress_completed_cycle"
  let gpCompAchieved ← reqOptNat fields "goal_progress_completed_achieved"
  let gpScore ← reqOptNat fields "goal_progress_score"
  checkBound "goal_progress_resolved" (gpResolved ≤ goalCount)
  checkBound "goal_progress_attempt" (gpAttempt ≤ attemptCap)
  checkBound "goal_progress_achieved" (gpAchieved ≤ gpResolved)
  checkBound "goal_progress_completed_achieved" (gpCompAchieved.all (· ≤ goalCount))
  checkBound "goal_progress_completed_cycle" (gpCompCycle.all (· ≤ gpCycle))
  checkBound "goal_progress_score" (gpScore.all (· < 1001))
  let currNames ← reqStrArr fields "curriculum_names" none
  let currFailed ← reqNatArr fields "curriculum_failed_attempts" none
  let currSuccess ← reqOptNatArr fields "curriculum_success_steps" none
  checkBound "curriculum_names" (currNames.size == goalCount)
  checkBound "curriculum_failed_attempts"
    (currFailed.size == goalCount && currFailed.all (· ≤ attemptCap))
  checkBound "curriculum_success_steps"
    (currSuccess.size == goalCount && currSuccess.all (fun s => s.all (· ≤ stepCap)))
  let worldStep ← reqNat fields "world_step"
  let seed ← reqNat fields "seed"
  let side ← reqNat fields "side"
  checkBound "side" (side > 0)
  let dayLength ← reqNat fields "day_length"
  let _regrow ← reqNat fields "regrow"
  let _foodInterval ← reqNat fields "food_interval"
  let _foodCap ← reqNat fields "food_cap"
  let _deerCap ← reqNat fields "deer_cap"
  let x ← reqInt fields "x"
  let y ← reqInt fields "y"
  let facing ← reqNat fields "facing"
  checkBound "facing" (facing < 4)
  let energy ← reqNat fields "energy"
  let wood ← reqNat fields "wood"
  let stone ← reqNat fields "stone"
  let food ← reqNat fields "food"
  let gold ← reqNat fields "gold"
  let axe ← reqBool fields "axe"
  let boat ← reqBool fields "boat"
  let action ← reqNat fields "action"
  checkBound "action" (action < FeatureConstants.primitiveCount)
  let reward ← reqScalar fields "reward"
  let done ← reqBool fields "done"
  let ev ← reqNat fields "ev"
  checkBound "ev" (ev < 64)
  let goal ← reqNat fields "goal"
  let attempt ← reqNat fields "attempt"
  let tier ← reqNat fields "tier"
  let cycle ← reqNat fields "cycle"
  let gkind ← reqNat fields "gkind"
  checkBound "gkind" (goalKindCodes.contains gkind)
  let gitem ← reqNat fields "gitem"
  checkBound "gitem" (goalItemCodes.contains gitem)
  let gx ← reqInt fields "gx"
  let gy ← reqInt fields "gy"
  let gn ← reqNat fields "gn"
  let tiles ← reqNatArr fields "tiles" (some 121)
  checkBound "tiles" (tiles.all (· < 8))
  let tileExtra ← reqNatArr fields "tile_extra" (some 121)
  checkBound "tile_extra" (tileExtra.all (· < 256))
  let terminal ← reqBool fields "end"
  let lifetimeStep ← reqNat fields "lifetime_step"
  let rewardRate ← reqScalar fields "reward_rate"
  let eps ← reqScalar fields "eps"
  let meanAlpha ← reqScalar fields "mean_alpha"
  let aCtl ← reqScalar fields "a_ctl"
  let aDem ← reqScalar fields "a_dem"
  let alphaControl ← reqScalarArr fields "alpha_control_all" (some 9)
  let alphaMeta ← reqScalarArr fields "alpha_meta_all" (some 4)
  let alphaOptions ← reqScalarArr fields "alpha_option_all" (some 27)
  let alphaDemons ← reqScalarArr fields "alpha_demon_all" (some 11)
  let alphaModels ← reqScalarArr fields "alpha_models" (some 9)
  let creditControl ← reqNatArr fields "credit_control" (some 9)
  let creditMeta ← reqNatArr fields "credit_meta" (some 4)
  let creditOptions ← reqNatArr fields "credit_options" (some 27)
  let creditDemons ← reqNatArr fields "credit_demons" (some 11)
  let creditModels ← reqNatArr fields "credit_models" (some 9)
  let optModRew ← reqScalarArr fields "option_model_rewards" (some 3)
  let optModCont ← reqScalarArr fields "option_model_continuations" (some 3)
  let optModDur ← reqScalarArr fields "option_model_durations" (some 3)
  let planningErrors ← reqScalarArr fields "planning_errors" (some 3)
  let planningSteps ← reqNat fields "planning_steps"
  let decisionSource ← reqStr fields "decision_source"
  checkBound "decision_source"
    (["primitive", "exploration_start", "exploration_continuation", "option"].contains decisionSource)
  let skill ← reqNat fields "skill"
  checkBound "skill" (skill < FeatureConstants.skillCount || skill == 255)
  let explored ← reqBool fields "explored"
  let controlValues ← reqScalarArr fields "control" (some 9)
  let metaValues ← reqScalarArr fields "meta" (some 4)
  let actionProbs ← reqScalarArr fields "action_probabilities" (some 9)
  let metaProbs ← reqScalarArr fields "meta_probabilities" (some 4)
  let metaAction ← reqNat fields "meta_action"
  checkBound "meta_action" (metaAction < FeatureConstants.metaActionCount || metaAction == 255)
  let optionStart ← reqNat fields "option_start"
  checkBound "option_start" (optionStart < FeatureConstants.skillCount || optionStart == 255)
  let optionEndSkill ← reqNat fields "option_end_skill"
  checkBound "option_end_skill" (optionEndSkill < FeatureConstants.skillCount || optionEndSkill == 255)
  let optionEndDuration ← reqNat fields "option_end_duration"
  let optionEndReason ← reqNat fields "option_end_reason"
  checkBound "option_end_reason" (optionEndReason < 3 || optionEndReason == 255)
  let optionElapsed ← reqNat fields "option_elapsed"
  let lifetimeRewardSum ← reqScalar fields "lifetime_reward_sum"
  let lifetimeRewardCount ← reqNat fields "lifetime_reward_count"
  let lifetimeRewardFamilySum ← reqScalarArr fields "lifetime_reward_family_sum" (some 4)
  let _lifetimeRewardFamilyCount ← reqNatArr fields "lifetime_reward_family_count" (some 4)
  let lifetimeRewardHistorySum ← reqScalarArr fields "lifetime_reward_history_sum" (some 64)
  let lifetimeRewardHistoryCount ← reqNatArr fields "lifetime_reward_history_count" (some 64)
  let lifetimeErrorHistorySum ← reqScalarArr fields "lifetime_error_history_sum" (some 64)
  let lifetimeErrorHistoryCount ← reqNatArr fields "lifetime_error_history_count" (some 64)
  let lifetimeErrorSum ← reqScalarArr fields "lifetime_error_sum" (some 11)
  let _lifetimeErrorCount ← reqNatArr fields "lifetime_error_count" (some 11)
  let settledReturn ← reqScalarArr fields "settled_return" (some 11)
  let settledError ← reqScalarArr fields "settled_error" (some 11)
  let lifetimeOptionStarted ← reqNatArr fields "lifetime_option_started" (some 3)
  let lifetimeOptionCompleted ← reqNatArr fields "lifetime_option_completed" (some 3)
  let lifetimeOptionDuration ← reqNatArr fields "lifetime_option_duration" (some 3)
  let lifetimeOptionEndReasons ← reqNatArr fields "lifetime_option_end_reasons" (some 9)
  let lifetimeGoalAttempts ← reqNatArr fields "lifetime_goal_attempts" (some 4)
  let lifetimeGoalSuccesses ← reqNatArr fields "lifetime_goal_successes" (some 4)
  let lifetimeGoalSteps ← reqNatArr fields "lifetime_goal_steps" (some 4)
  let lifetimeCycleAttempts ← reqNatArr fields "lifetime_cycle_attempts" (some 64)
  let lifetimeCycleSuccesses ← reqNatArr fields "lifetime_cycle_successes" (some 64)
  let lifetimeCycleSteps ← reqNatArr fields "lifetime_cycle_steps" (some 64)
  let agVersion ← reqNat fields "agreement_version"
  checkExact "agreement_version" agVersion 1
  let agScale ← reqNat fields "agreement_scale"
  checkExact "agreement_scale" agScale Agreement.displayScale
  let agStarted ← reqOptNat fields "agreement_started"
  let agStopped ← reqBool fields "agreement_stopped"
  let agScore ← reqOptNat fields "agreement_score"
  checkBound "agreement_score" (agScore.all (· ≤ Agreement.displayScale))
  let agText ← reqOptStr fields "agreement_text"
  let agError ← reqOptNat fields "agreement_error"
  checkBound "agreement_error" (agError.all (· ≤ Agreement.displayScale))
  let agChScore ← reqOptNatArr fields "agreement_channel_score" (some 11)
  checkBound "agreement_channel_score" (agChScore.all (·.all (· ≤ Agreement.displayScale)))
  let agChText ← reqOptStrArr fields "agreement_channel_text" (some 11)
  let agChError ← reqOptNatArr fields "agreement_channel_error" (some 11)
  checkBound "agreement_channel_error" (agChError.all (·.all (· ≤ Agreement.displayScale)))
  let agCount ← reqStrArr fields "agreement_count" (some 11)
  checkBound "agreement_count" (agCount.all (isDecimalUpTo Agreement.countLimit))
  let agPending ← reqNatArr fields "agreement_pending" (some 11)
  checkBound "agreement_pending" (agPending.all (· ≤ FeatureConstants.pendingSamples))
  let agCensored ← reqStrArr fields "agreement_censored" (some 11)
  checkBound "agreement_censored" (agCensored.all (isDecimalUpTo Agreement.countLimit))
  let agStatus ← reqStrArr fields "agreement_status" (some 11)
  checkBound "agreement_status" (agStatus.all fun s =>
    ["invalid", "saturated", "partially censored", "censored", "pending", "complete", "empty"].contains s)
  let agHorizon ← reqNatArr fields "agreement_horizon" (some 11)
  checkBound "agreement_horizon" (agHorizon.all (· ≤ FeatureConstants.maxSettlement))
  let agStartFirst ← reqOptNatArr fields "agreement_start_first" (some 11)
  let agStartLast ← reqOptNatArr fields "agreement_start_last" (some 11)
  let agSettleFirst ← reqOptNatArr fields "agreement_settlement_first" (some 11)
  let agSettleLast ← reqOptNatArr fields "agreement_settlement_last" (some 11)
  let agTail ← reqOptNatArr fields "agreement_tail" (some 11)
  checkBound "agreement_tail" (agTail.all (·.all (· ≤ Agreement.displayScale)))
  let agRounding ← reqOptNatArr fields "agreement_rounding" (some 11)
  checkBound "agreement_rounding" (agRounding.all (·.all (· ≤ Agreement.displayScale)))
  let agHistClock ← reqOptNatArr fields "agreement_history_clock" (some 64)
  let agHistScore ← reqOptNatArr fields "agreement_history_score" (some 64)
  checkBound "agreement_history_score" (agHistScore.all (·.all (· ≤ Agreement.displayScale)))
  let _ckptFmt ← reqNat fields "checkpoint_format"
  let controlCriterion ← reqNat fields "control_criterion"
  checkBound "control_criterion" (controlCriterion < 2)
  let weightSpace ← reqNat fields "weight_space"
  checkExact "primitive_count" (← reqNat fields "primitive_count") FeatureConstants.primitiveCount
  checkExact "meta_count" (← reqNat fields "meta_count") FeatureConstants.metaActionCount
  checkExact "skill_count" (← reqNat fields "skill_count") FeatureConstants.skillCount
  checkExact "option_end_count" (← reqNat fields "option_end_count") 3
  checkExact "demon_count" (← reqNat fields "demon_count") FeatureConstants.demonCount
  checkExact "learner_count" (← reqNat fields "learner_count") telemetryLearnerCount
  checkExact "history_bins" (← reqNat fields "history_bins") FeatureConstants.historyBins
  checkExact "cycle_bins" (← reqNat fields "cycle_bins") FeatureConstants.cycleBins
  checkExact "exact_cycles" (← reqNat fields "exact_cycles") FeatureConstants.exactCycles
  let settleStride ← reqNat fields "settle_stride"
  let settleRemaining ← reqScalar fields "settle_remaining"
  let nTilings ← reqNat fields "n_tilings"
  let imprintUnits ← reqNat fields "imprint_units"
  let retireStep ← reqOptNat fields "retire_step"
  checkBound "retire_step" (retireStep.all (· ≤ lifetimeStep))
  let retireUnit ← reqOptNat fields "retire_unit"
  checkBound "retire_unit" (retireUnit.all (· < imprintUnits))
  let retireCount ← reqNat fields "retire_count"
  let subtaskPolicy ← reqStr fields "subtask_policy"
  checkBound "subtask_policy" (["learned", "hand_authored"].contains subtaskPolicy)
  let subtaskUnit ← reqOptNatArr fields "subtask_unit" (some 3)
  checkBound "subtask_unit" (subtaskUnit.all fun u => u.all fun idx => idx < imprintUnits && idx < 2 ^ 31)
  let subtaskBonus ← reqScalarArr fields "subtask_bonus" (some 3)
  let actionNames ← reqStrArr fields "action_names" (some 9)
  let metaNames ← reqStrArr fields "meta_names" (some 4)
  let skillNames ← reqStrArr fields "skill_names" (some 3)
  let goalFamilyNames ← reqStrArr fields "goal_family_names" (some 4)
  let demons ← reqScalarArr fields "demons" (some 11)
  let cums ← reqScalarArr fields "cums" (some 11)
  let demonNames ← reqStrArr fields "demon_names" (some 11)
  let demonTargetPolicy ← reqStrArr fields "demon_target_policy" (some 11)
  let demonGamma ← reqScalarArr fields "demon_gamma" (some 11)
  let demonHorizon ← reqScalarArr fields "demon_horizon" (some 11)
  let nonFiniteKey := firstNonFinite [
    ("reward", reward.isFinite),
    ("reward_rate", rewardRate.isFinite),
    ("eps", eps.isFinite),
    ("mean_alpha", meanAlpha.isFinite),
    ("a_ctl", aCtl.isFinite),
    ("a_dem", aDem.isFinite),
    ("alpha_control_all", allFinite alphaControl),
    ("alpha_meta_all", allFinite alphaMeta),
    ("alpha_option_all", allFinite alphaOptions),
    ("alpha_demon_all", allFinite alphaDemons),
    ("alpha_models", allFinite alphaModels),
    ("option_model_rewards", allFinite optModRew),
    ("option_model_continuations", allFinite optModCont),
    ("option_model_durations", allFinite optModDur),
    ("planning_errors", allFinite planningErrors),
    ("control", allFinite controlValues),
    ("meta", allFinite metaValues),
    ("action_probabilities", allFinite actionProbs),
    ("meta_probabilities", allFinite metaProbs),
    ("lifetime_reward_sum", lifetimeRewardSum.isFinite),
    ("lifetime_reward_family_sum", allFinite lifetimeRewardFamilySum),
    ("lifetime_reward_history_sum", allFinite lifetimeRewardHistorySum),
    ("lifetime_error_history_sum", allFinite lifetimeErrorHistorySum),
    ("lifetime_error_sum", allFinite lifetimeErrorSum),
    ("settled_return", allFinite settledReturn),
    ("settled_error", allFinite settledError),
    ("settle_remaining", settleRemaining.isFinite),
    ("subtask_bonus", allFinite subtaskBonus),
    ("demons", allFinite demons),
    ("cums", allFinite cums),
    ("demon_gamma", allFinite demonGamma),
    ("demon_horizon", allFinite demonHorizon)]
  let aMeta := meanPositiveScaled alphaMeta.toList
  let aOpt := meanPositiveScaled alphaOptions.toList
  let summary : FrameSummary := {
    runId, agentEpoch, origin, timestampMs, worldStep, lifetimeStep, side, dayLength,
    x, y, facing, action, reward, done, terminal, goal, cycle, decisionSource, skill, explored,
    optionStart, optionEndSkill, optionEndReason, eps, updateUs, environmentUs,
    aCtl, aDem, aMeta, aOpt, nonFiniteKey
  }
  let goalProgress : GoalProgressSnapshot := {
    goalCount, attemptCap, stepCap, invalid := gpInvalid, cycle := gpCycle,
    resolved := gpResolved, attempt := gpAttempt, achieved := gpAchieved,
    completedCycle := gpCompCycle, completedAchieved := gpCompAchieved, score := gpScore,
    curriculumNames := currNames, curriculumFailed := currFailed,
    curriculumSuccessSteps := currSuccess, activeGoal := goal
  }
  let agreement : AgreementSnapshot := {
    sourceSha, buildSha, processStartedMs, clock := lifetimeStep, scale := agScale,
    started := agStarted, stopped := agStopped, score := agScore, text := agText, error := agError,
    channelScore := agChScore, channelText := agChText, channelError := agChError,
    count := agCount, pending := agPending, censored := agCensored, status := agStatus,
    horizon := agHorizon, startFirst := agStartFirst, startLast := agStartLast,
    settlementFirst := agSettleFirst, settlementLast := agSettleLast,
    tail := agTail, rounding := agRounding, historyClock := agHistClock,
    historyScore := agHistScore, settleStride, demonNames, demonTargetPolicy,
    demonGamma, demonHorizon, goalProgress
  }
  return {
    summary, sourceSha, buildSha, auditDigest, seed, energy, wood, stone, food, gold, axe, boat,
    ev, attempt, tier, gkind, gitem, gx, gy, gn, tiles, tileExtra, rewardRate, controlCriterion,
    processUptimeMs, coreRssBytes, checkpointBytes, checkpointWriteUs, checkpointFailures,
    telemetryRefusals, telemetryDrops, weightSpace, nTilings, imprintUnits, retireStep, retireUnit,
    retireCount, subtaskPolicy, subtaskUnit, subtaskBonus, actionNames, metaNames, skillNames,
    goalFamilyNames, controlValues, metaValues, actionProbs, metaProbs, metaAction, optionElapsed,
    optionEndDuration, optionModelRewards := optModRew, optionModelContinuations := optModCont,
    optionModelDurations := optModDur, planningSteps, planningErrors, alphaControl, alphaMeta,
    alphaOptions, alphaDemons, alphaModels, creditControl, creditMeta, creditOptions, creditDemons,
    creditModels, demons, cums, settledReturn, settledError, lifetimeRewardSum,
    lifetimeRewardCount, lifetimeRewardHistorySum, lifetimeRewardHistoryCount,
    lifetimeErrorHistorySum, lifetimeErrorHistoryCount, lifetimeOptionStarted,
    lifetimeOptionCompleted, lifetimeOptionDuration, lifetimeOptionEndReasons,
    lifetimeGoalAttempts, lifetimeGoalSuccesses, lifetimeGoalSteps, lifetimeCycleAttempts,
    lifetimeCycleSuccesses, lifetimeCycleSteps, agreement
  }

def agreementSnapshotFollows (prev next : AgreementSnapshot) : Bool :=
  let n := next.goalProgress
  let p := prev.goalProgress
  ClockProgram.snapshotFollows.eval fun i =>
    match i.val with
    | 0 => next.processStartedMs
    | 1 => next.clock
    | 2 => if next.stopped then 1 else 0
    | 3 => n.cycle
    | 4 => n.resolved
    | 5 => n.attempt
    | 6 => if n.invalid then 1 else 0
    | 7 => prev.processStartedMs
    | 8 => prev.clock
    | 9 => if prev.stopped then 1 else 0
    | 10 => p.cycle
    | 11 => p.resolved
    | 12 => p.attempt
    | _ => if p.invalid then 1 else 0

def admitAgreementSnapshot (previous : Option AgreementSnapshot) (next : AgreementSnapshot) :
    AgreementSnapshot :=
  match previous with
  | none => next
  | some prev => if agreementSnapshotFollows prev next then next else prev

theorem agreementSnapshotFollows_final (prev next : AgreementSnapshot)
    (hProc : next.processStartedMs = prev.processStartedMs)
    (hClock : next.clock = prev.clock)
    (hPrevOpen : prev.stopped = false)
    (hNextStopped : next.stopped = true) :
    agreementSnapshotFollows prev next = true := by
  have h7 : (7 : Fin 14).val = 7 := rfl
  have h8 : (8 : Fin 14).val = 8 := rfl
  have h9 : (9 : Fin 14).val = 9 := rfl
  simp [agreementSnapshotFollows, ClockProgram.snapshotFollows,
    ClockProgram.Predicate.eval, ClockProgram.Term.eval,
    h7, h8, h9, hProc, hClock, hPrevOpen, hNextStopped]

private def subtaskSignature (frame : ServerFrame) : String :=
  frame.subtaskPolicy ++ "|" ++
    String.intercalate "," (frame.subtaskUnit.toList.map fun u =>
      match u with | none => "-" | some n => toString n) ++ "|" ++
    String.intercalate "," (frame.subtaskBonus.toList.map fun s => s.formatFixed 3)

private def computeSurprise (prev : Option (Nat × Array Scalar)) (frame : ServerFrame) :
    Option Decimal := do
  let (prevWorld, prevDemons) ← prev
  guard (ClockProgram.worldSuccessor.eval (fun i =>
    if i.val == 0 then frame.summary.worldStep else prevWorld))
  guard (prevDemons.size == 11 && frame.demons.size == 11 &&
    frame.cums.size == 11 && frame.agreement.demonGamma.size == 11)
  let mut sumAbs : Int := 0
  let mut count : Nat := 0
  for idx in [:11] do
    if h1 : idx < frame.cums.size then
      if h2 : idx < frame.agreement.demonGamma.size then
        if h3 : idx < frame.demons.size then
          if h4 : idx < prevDemons.size then
            match frame.cums[idx], frame.agreement.demonGamma[idx], frame.demons[idx], prevDemons[idx] with
            | .finite c, .finite g, .finite pNow, .finite pPrev =>
              let some cs := c.scaled? 6 | failure
              let some gs := g.scaled? 6 | failure
              let some pNowS := pNow.scaled? 6 | failure
              let some pPrevS := pPrev.scaled? 6 | failure
              let prod := (gs * pNowS) / 1000000
              let residual := cs + prod - pPrevS
              sumAbs := sumAbs + (residual.natAbs : Int)
              count := count + 1
            | _, _, _, _ => failure
  if count == 0 then none
  else
    let avg := sumAbs / (count : Int)
    some ⟨false, avg.natAbs, -6⟩

structure DecodedTelemetry where
  identity : Option CoreIdentity
  health : Option Capture
  frame : Option (Except (BrowserRefusal × String) ServerFrame)
  subtaskSig : Option String
  sensed : Option Sensed

def decodeTelemetry (text : WireText) : DecodedTelemetry :=
  match (Json.parse text.val).toOption with
  | none => ⟨none, none, none, none, none⟩
  | some value =>
    let identity := (coreIdentityFromJson value).toOption
    let health := (healthFromJson value).toOption
    let frame := decodeServerFrame value
    let subtaskSig := match frame with
      | .ok f => some (subtaskSignature f)
      | .error _ => none
    let sensed := (sensedFromJson value).toOption
    ⟨identity, health, some frame, subtaskSig, sensed⟩

def ServerObserverState.observe (state : ServerObserverState) (decoded : DecodedTelemetry)
    (nowMonoMs : Nat) : ServerObserverState :=
  let (freshCapture, healthAdmission) := match decoded.health with
    | some capture => state.healthAdmission.receive capture
    | none => (false, state.healthAdmission)
  let state := { state with healthAdmission }
  let state := if freshCapture then
    { state with
      lastFreshMonoMs := some nowMonoMs
      captureRate := state.captureRate.record nowMonoMs }
    else state
  match decoded.frame with
  | none => state
  | some (.error (reason, key)) =>
    { state with
      refusedCount := state.refusedCount + 1
      lastRefusal := some ⟨reason, key⟩ }
  | some (.ok frame) =>
    if frame.summary.runId != runHex state.identity.run ||
        frame.summary.agentEpoch != state.identity.agentEpoch.toNat then
      state
    else
      let capture : Capture := {
        run := state.identity.run
        epoch := frame.summary.agentEpoch.toUInt64
        timestamp := frame.summary.timestampMs.toUInt64
        lifetime := frame.summary.lifetimeStep.toUInt64
        world := frame.summary.worldStep.toUInt64
        terminal := frame.summary.terminal
      }
      let (intake, admission) := state.admission.receive capture
      let agreement := some (admitAgreementSnapshot state.agreement frame.agreement)
      let state := { state with admission, agreement }
      let state := if freshCapture && (intake == .stored || intake == .rewound) then
          { state with lastFreshOrigin := some frame.summary.origin }
        else state
      match intake with
      | .skipped | .rewound => state
      | .stored =>
        let admittedCount := state.admittedCount + 1
        let nonFiniteCount := state.nonFiniteCount +
          if frame.summary.nonFiniteKey.isSome then 1 else 0
        let lastNonFiniteKey := frame.summary.nonFiniteKey.or state.lastNonFiniteKey
        let retireChangedAt :=
          match state.lastRetireCount with
          | some prev => if prev != frame.retireCount then some admittedCount else state.retireChangedAt
          | none => state.retireChangedAt
        let sig := decoded.subtaskSig.getD (subtaskSignature frame)
        let subtaskChangedAt :=
          match state.lastSubtaskSig with
          | some prev => if prev != sig then some admittedCount else state.subtaskChangedAt
          | none => state.subtaskChangedAt
        let planningChangedAt :=
          match state.lastPlanningSteps with
          | some prev => if prev != frame.planningSteps then some admittedCount else state.planningChangedAt
          | none => state.planningChangedAt
        let samples :=
          if admittedCount % verifyStride == 1 then
            let aDem := match frame.summary.aDem with
              | .finite d => if d.isPositive then some d else none
              | .nonFinite => none
            let aCtl := match frame.summary.aCtl with
              | .finite d => if d.isPositive then some d else none
              | .nonFinite => none
            let sample : HistorySample := {
              aDem, aCtl, aMeta := frame.summary.aMeta, aOpt := frame.summary.aOpt,
              surprise := computeSurprise state.prevDemons frame
            }
            state.samples.retain sample
          else state.samples
        { state with
          summaries := state.summaries.retain frame.summary
          latest := some frame
          samples
          admittedCount
          nonFiniteCount
          lastNonFiniteKey
          lastRetireCount := some frame.retireCount
          retireChangedAt
          lastSubtaskSig := some sig
          subtaskChangedAt
          lastPlanningSteps := some frame.planningSteps
          planningChangedAt
          prevDemons := some (frame.summary.worldStep, frame.demons) }

def ServerObserverState.framesPerSecondTenths (state : ServerObserverState) (nowMonoMs : Nat) :
    Option Nat :=
  state.captureRate.framesPerSecondTenths nowMonoMs

def ServerObserverState.streamLiveness (state : ServerObserverState)
    (lifecycle : Lifecycle) (unaskedStop : Bool) (runningSinceMonoMs : Option Nat)
    (nowMonoMs : Nat) : StreamLiveness :=
  if unaskedStop then .fault lifecycle.exhausted
  else
    match lifecycle.phaseValue with
    | .running _ =>
      match state.lastFreshMonoMs with
      | some last =>
        if nowMonoMs - last ≥ BrowserConstant.staleAfter.value then .stale true
        else .live
      | none =>
        match runningSinceMonoMs with
        | some started =>
          if nowMonoMs - started ≥ BrowserConstant.staleAfter.value then .stale false
          else .waitingForCapture
        | none => .waitingForCapture
    | .starting _ => .busy "starting…"
    | .stopping _ => .busy "stopping…"
    | .archiving => .busy "clearing…"
    | .idle => .idle

def ServerObserverState.beginRunningGeneration (state : ServerObserverState) :
    ServerObserverState :=
  { state with
    lastFreshMonoMs := none
    lastFreshOrigin := none
    captureRate := {} }

def ServerObserverState.resetIdentity (state : ServerObserverState) (identity : Identity) :
    ServerObserverState :=
  if state.identity == identity then state else .empty identity

private theorem capture_follows_same_clocks (next prev : Capture)
    (hLife : next.lifetime = prev.lifetime) (hWorld : next.world = prev.world) :
    next.follows prev = false := by
  have h3 : (3 : Fin 6).val = 3 := rfl
  have h4 : (4 : Fin 6).val = 4 := rfl
  simp [Capture.follows, ClockProgram.follows, ClockProgram.Predicate.eval,
    ClockProgram.Term.eval, h3, h4, hLife, hWorld]

theorem ServerObserverState.observe_same_clock_final_agreement
    (state : ServerObserverState) (decoded : DecodedTelemetry) (frame : ServerFrame)
    (prevCap : Capture) (prevAg : AgreementSnapshot) (nowMonoMs : Nat)
    (hFrame : decoded.frame = some (.ok frame))
    (hRun : frame.summary.runId = runHex state.identity.run)
    (hEpoch : frame.summary.agentEpoch = state.identity.agentEpoch.toNat)
    (hPrevCap : state.admission.previous = some prevCap)
    (hLife : frame.summary.lifetimeStep.toUInt64 = prevCap.lifetime)
    (hWorld : frame.summary.worldStep.toUInt64 = prevCap.world)
    (hPrevAg : state.agreement = some prevAg)
    (hProc : frame.agreement.processStartedMs = prevAg.processStartedMs)
    (hClock : frame.agreement.clock = prevAg.clock)
    (hPrevOpen : prevAg.stopped = false)
    (hNextStopped : frame.agreement.stopped = true) :
    let next := state.observe decoded nowMonoMs
    next.agreement = some frame.agreement ∧
      next.summaries = state.summaries ∧
      next.samples = state.samples ∧
      next.admittedCount = state.admittedCount ∧
      next.latest = state.latest ∧
      next.prevDemons = state.prevDemons ∧
      next.admission.previous = state.admission.previous := by
  dsimp only
  unfold ServerObserverState.observe
  have hIdOk : (frame.summary.runId != runHex state.identity.run ||
      frame.summary.agentEpoch != state.identity.agentEpoch.toNat) = false := by
    simp [hRun, hEpoch]
  have hAgOk : admitAgreementSnapshot state.agreement frame.agreement = frame.agreement := by
    simp [admitAgreementSnapshot, hPrevAg,
      agreementSnapshotFollows_final prevAg frame.agreement hProc hClock hPrevOpen hNextStopped]
  have hEpochEq : frame.summary.agentEpoch.toUInt64 = state.identity.agentEpoch := by
    rw [hEpoch]
    exact UInt64.ofNat_toNat
  let cap : Capture := {
    run := state.identity.run
    epoch := frame.summary.agentEpoch.toUInt64
    timestamp := frame.summary.timestampMs.toUInt64
    lifetime := frame.summary.lifetimeStep.toUInt64
    world := frame.summary.worldStep.toUInt64
    terminal := frame.summary.terminal
  }
  have hMatches : cap.matches state.identity = true := by
    simp [Capture.matches, cap, hEpochEq]
  have hNotFollows : cap.follows prevCap = false :=
    capture_follows_same_clocks cap prevCap hLife hWorld
  have hReceiveRew :
      state.admission.newestTimestamp.all (cap.timestamp > ·) = true →
      state.admission.receive cap = (.rewound, state.admission.noteTimestamp cap.timestamp) := by
    intro hFresh
    unfold Admission.receive
    simp [hMatches, hPrevCap, hNotFollows, hFresh]
  have hReceiveSkip :
      state.admission.newestTimestamp.all (cap.timestamp > ·) = false →
      state.admission.receive cap = (.skipped, state.admission.noteTimestamp cap.timestamp) := by
    intro hFresh
    unfold Admission.receive
    simp [hMatches, hPrevCap, hNotFollows, hFresh]
  rcases hHealth :
      (match decoded.health with
       | some capture => state.healthAdmission.receive capture
       | none => (false, state.healthAdmission)) with ⟨freshCap, healthAdm⟩
  rw [hHealth, hFrame]
  cases freshCap with
  | false =>
    dsimp only
    rw [ite_eq_right Bool.false_ne_true]
    dsimp only
    rw [ite_eq_right (by simp [hIdOk])]
    cases hFreshTs : state.admission.newestTimestamp.all (cap.timestamp > ·) with
    | true =>
      have hRec := hReceiveRew hFreshTs
      dsimp only [cap] at hRec
      rw [hRec]
      dsimp only
      rw [ite_eq_right (by decide)]
      simp [hAgOk, Admission.noteTimestamp, hPrevCap]
    | false =>
      have hRec := hReceiveSkip hFreshTs
      dsimp only [cap] at hRec
      rw [hRec]
      dsimp only
      rw [ite_eq_right (by decide)]
      simp [hAgOk, Admission.noteTimestamp, hPrevCap]
  | true =>
    dsimp only
    rw [ite_eq_left rfl]
    dsimp only
    rw [ite_eq_right (by simp [hIdOk])]
    cases hFreshTs : state.admission.newestTimestamp.all (cap.timestamp > ·) with
    | true =>
      have hRec := hReceiveRew hFreshTs
      dsimp only [cap] at hRec
      rw [hRec]
      dsimp only
      rw [ite_eq_left (by decide)]
      simp [hAgOk, Admission.noteTimestamp, hPrevCap]
    | false =>
      have hRec := hReceiveSkip hFreshTs
      dsimp only [cap] at hRec
      rw [hRec]
      dsimp only
      rw [ite_eq_right (by decide)]
      simp [hAgOk, Admission.noteTimestamp, hPrevCap]

theorem CaptureRate.framesPerSecondTenths_unbounded (r : CaptureRate) (sec count : Nat)
    (hBucket : r.hasBucket = true) (hPrev : r.hasPrevious = true)
    (hSec : r.bucketSec = sec) (hPrevCount : r.previousCount = count)
    (hCurCount : r.currentCount = 0) :
    r.framesPerSecondTenths (sec * 1000) = some (count * 10) := by
  have hDiv : (sec * 1000) / 1000 = sec := Nat.mul_div_cancel sec (by decide)
  have hMod : (sec * 1000) % 1000 = 0 := Nat.mul_mod_left sec 1000
  simp only [CaptureRate.framesPerSecondTenths, hBucket, hPrev, hSec, hPrevCount, hCurCount,
    hDiv, hMod, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true, Nat.add_zero]
  have hArith : count * 10000 / 1000 = count * 10 := by
    rw [show count * 10000 = (count * 10) * 1000 by rw [Nat.mul_assoc]]
    exact Nat.mul_div_cancel (count * 10) (by decide)
  rw [hArith]

theorem ServerObserverState.streamLiveness_live_requires_fresh
    (state : ServerObserverState) (lifecycle : Lifecycle) (unaskedStop : Bool)
    (runningSinceMonoMs : Option Nat) (nowMonoMs : Nat)
    (hLive : state.streamLiveness lifecycle unaskedStop runningSinceMonoMs nowMonoMs = .live) :
    unaskedStop = false ∧ (∃ gen, lifecycle.phaseValue = .running gen) ∧
      ∃ last, state.lastFreshMonoMs = some last ∧ nowMonoMs - last < BrowserConstant.staleAfter.value := by
  unfold ServerObserverState.streamLiveness at hLive
  cases hUnasked : unaskedStop with
  | true => simp [hUnasked] at hLive
  | false =>
    simp only [hUnasked, Bool.false_eq_true, ↓reduceIte] at hLive
    cases hPhase : lifecycle.phaseValue with
    | idle | starting _ | stopping _ | archiving => simp [hPhase] at hLive
    | running gen =>
      simp only [hPhase] at hLive
      cases hLast : state.lastFreshMonoMs with
      | none =>
        simp only [hLast] at hLive
        cases runningSinceMonoMs with
        | none => cases hLive
        | some started =>
          dsimp only at hLive
          split at hLive <;> cases hLive
      | some last =>
        simp only [hLast] at hLive
        split at hLive
        · cases hLive
        · rename_i hNotStale
          exact ⟨rfl, ⟨gen, rfl⟩, ⟨last, rfl, Nat.lt_of_not_le hNotStale⟩⟩

theorem ServerObserverState.streamLiveness_no_capture_stale
    (state : ServerObserverState) (lifecycle : Lifecycle) (gen : UInt64) (started nowMonoMs : Nat)
    (hPhase : lifecycle.phaseValue = .running gen)
    (hNoFresh : state.lastFreshMonoMs = none)
    (hElapsed : nowMonoMs - started ≥ BrowserConstant.staleAfter.value) :
    state.streamLiveness lifecycle false (some started) nowMonoMs = .stale false := by
  simp [ServerObserverState.streamLiveness, hPhase, hNoFresh, hElapsed]

end Acorn.Host.Viewer
