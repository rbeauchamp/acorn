import Acorn.Host.Viewer.BrowserRecord
import Acorn.Host.Viewer.WorldMemory

namespace Acorn.Host.Viewer

inductive BrowserConstant where
  | schema
  | unseen
  | mapSide
  | tileKinds
  | demons
  | primitives
  | metaActions
  | patch
  | skills
  | optionEnds
  | goalFamilies
  | modelHeads
  | historyBins
  | cycleBins
  | exactCycles
  | readPace
  | statsWindow
  | frameCapacity
  | ribbonSpan
  | staleAfter
  | tilePixels

def BrowserConstant.name : BrowserConstant → String
  | .schema => "SCHEMA" | .unseen => "UNSEEN" | .mapSide => "MAX_MAP_SIDE"
  | .tileKinds => "N_KIND" | .demons => "N_DEM" | .primitives => "N_CTL"
  | .metaActions => "N_META" | .patch => "N_TILE" | .skills => "N_SKILL"
  | .optionEnds => "N_OPTION_END" | .goalFamilies => "N_GOAL_FAMILY"
  | .modelHeads => "N_MODEL" | .historyBins => "HISTORY_BINS"
  | .cycleBins => "CYCLE_BINS" | .exactCycles => "EXACT_CYCLES"
  | .readPace => "READ_MS" | .statsWindow => "WIN" | .frameCapacity => "CAP"
  | .ribbonSpan => "RIBBON_SPAN" | .staleAfter => "STALE_MS" | .tilePixels => "Z"

def BrowserConstant.value : BrowserConstant → Nat
  | .schema => telemetrySchemaVersion
  | .unseen => (MapCell.byte none).toNat
  | .mapSide => mapSideCapacity
  | .tileKinds => 8
  | .demons => FeatureConstants.demonCount
  | .primitives => FeatureConstants.primitiveCount
  | .metaActions => FeatureConstants.metaActionCount
  | .patch => FeatureConstants.patchSide * FeatureConstants.patchSide
  | .skills => FeatureConstants.skillCount
  | .optionEnds => 3
  | .goalFamilies => 4
  | .modelHeads => 3
  | .historyBins => FeatureConstants.historyBins
  | .cycleBins => FeatureConstants.cycleBins
  | .exactCycles => FeatureConstants.exactCycles
  | .readPace => 250
  | .statsWindow => 1000
  | .frameCapacity => 30000
  | .ribbonSpan => 3000
  | .staleAfter => 8000
  | .tilePixels => 4

def BrowserConstant.all : List BrowserConstant :=
  [.schema, .unseen, .mapSide, .tileKinds, .demons, .primitives, .metaActions, .patch,
   .skills, .optionEnds, .goalFamilies, .modelHeads, .historyBins, .cycleBins, .exactCycles,
   .readPace, .statsWindow, .frameCapacity, .ribbonSpan, .staleAfter, .tilePixels]

theorem BrowserConstant.all_complete (constant : BrowserConstant) :
    constant ∈ BrowserConstant.all := by
  cases constant <;> simp [BrowserConstant.all]

theorem BrowserConstant.metaActions_skills :
    BrowserConstant.metaActions.value = BrowserConstant.skills.value + 1 := by
  decide

theorem BrowserConstant.names_distinct : (BrowserConstant.all.map (·.name)).Nodup := by
  decide

def BrowserConstant.product (stride : List BrowserConstant) : Nat :=
  stride.foldl (fun width constant => width * constant.value) 1

def browserTags (key : String) : List String :=
  (browserRules.findSome? fun (name, rule) =>
    match rule with
    | .tags values => if name = key then some values else none
    | _ => none).getD []

def browserElementBound (key : String) : Option Nat :=
  browserRules.findSome? fun (name, rule) =>
    match rule with
    | .each (.range upper) => if name = key then some upper else none
    | _ => none

theorem BrowserConstant.tileKinds_admitted :
    browserElementBound "tiles" = some BrowserConstant.tileKinds.value := by
  decide +kernel

def browserAbsentCodes : List (String × Nat) :=
  browserRules.filterMap fun (key, rule) =>
    match rule with
    | .either _ (.exact code) => some (key, code)
    | _ => none

theorem BrowserConstant.unseen_admitted :
    browserAbsentCodes =
      ["skill", "option_start", "option_end_skill", "option_end_reason", "meta_action"].map
        fun key => (key, BrowserConstant.unseen.value) := by
  decide +kernel

inductive BrowserEncoding where
  | number
  | flag
  | tag
  | sum
  | text
  | values (stride : List BrowserConstant)
  | bytes (stride : List BrowserConstant)
  | cycleBin

structure BrowserColumn where
  name : String
  encoding : BrowserEncoding

def browserCycleKey : String := "cycle"

theorem browserCycleKey_admitted :
    (browserCycleKey, TelemetryShape.natural) ∈ browserSchema := by
  decide +kernel

def BrowserColumn.fits (key : String) (column : BrowserColumn) (shape : TelemetryShape) :
    Bool :=
  let conversion := browserConversion key shape
  match column.encoding with
  | .number => conversion.number shape
  | .flag =>
    (match shape with
      | .flag => true
      | _ => false)
  | .tag =>
    (match shape with
      | .text => !(browserTags key).isEmpty
      | _ => false)
  | .text =>
    (match shape with
      | .text => true
      | _ => false)
  | .sum => (conversion.numbers shape).isSome
  | .values stride => conversion.numbers shape == some (BrowserConstant.product stride)
  | .bytes stride =>
    conversion.numbers shape == some (BrowserConstant.product stride) &&
      (match browserElementBound key with
        | some upper => decide (upper ≤ 256)
        | none => false)
  | .cycleBin =>
    conversion.numbers shape ==
      some (BrowserConstant.goalFamilies.value * BrowserConstant.cycleBins.value)

private def ring (key name : String) (encoding : BrowserEncoding) :
    String × BrowserColumn :=
  (key, ⟨name, encoding⟩)

def browserColumns : List (String × BrowserColumn) :=
  [ring "run_id" "runId" .text, ring "agent_epoch" "agentEpoch" .number,
   ring "origin" "origin" .tag, ring "update_us" "updateUs" .number,
   ring "environment_us" "environmentUs" .number,
   ring "goal_count" "goalCount" .number, ring "attempt_cap" "attemptCap" .number,
   ring "world_step" "worldStep" .number, ring "x" "x" .number, ring "y" "y" .number,
   ring "facing" "facing" .number, ring "energy" "energy" .number,
   ring "wood" "wood" .number, ring "stone" "stone" .number,
   ring "food" "food" .number, ring "gold" "gold" .number, ring "axe" "axe" .flag,
   ring "boat" "boat" .flag, ring "action" "action" .number,
   ring "reward" "reward" .number, ring "done" "done" .flag, ring "ev" "ev" .number,
   ring "goal" "goal" .number, ring "attempt" "attempt" .number,
   ring "tier" "tier" .number, ring "cycle" "cycle" .number,
   ring "gkind" "gkind" .number, ring "gitem" "gitem" .number,
   ring "gx" "gx" .number, ring "gy" "gy" .number, ring "gn" "gn" .number,
   ring "tiles" "tiles" (.bytes [.patch]), ring "tile_extra" "extra" (.bytes [.patch]),
   ring "end" "end" .flag, ring "lifetime_step" "lifetimeStep" .number,
   ring "reward_rate" "rewardRate" .number, ring "eps" "eps" .number,
   ring "mean_alpha" "alpha" .number, ring "a_ctl" "aCtl" .number,
   ring "a_dem" "aDem" .number,
   ring "alpha_control_all" "alphaControl" (.values [.primitives]),
   ring "alpha_meta_all" "alphaMeta" (.values [.metaActions]),
   ring "alpha_option_all" "alphaOptions" (.values [.primitives, .skills]),
   ring "alpha_demon_all" "alphaDemons" (.values [.demons]),
   ring "alpha_models" "alphaModels" (.values [.modelHeads, .skills]),
   ring "credit_control" "creditControl" (.values [.primitives]),
   ring "credit_meta" "creditMeta" (.values [.metaActions]),
   ring "credit_options" "creditOptions" (.values [.primitives, .skills]),
   ring "credit_demons" "creditDemons" (.values [.demons]),
   ring "credit_models" "creditModels" (.values [.modelHeads, .skills]),
   ring "option_model_rewards" "optModRew" (.values [.skills]),
   ring "option_model_continuations" "optModCont" (.values [.skills]),
   ring "option_model_durations" "optModDuration" (.values [.skills]),
   ring "planning_errors" "planningErrors" (.values [.skills]),
   ring "planning_steps" "planningSteps" .number,
   ring "decision_source" "decisionSource" .tag, ring "skill" "skill" .number,
   ring "explored" "explored" .flag, ring "control" "ctl" (.values [.primitives]),
   ring "meta" "met" (.values [.metaActions]),
   ring "action_probabilities" "actProb" (.values [.primitives]),
   ring "meta_probabilities" "metaProb" (.values [.metaActions]),
   ring "meta_action" "metaAction" .number,
   ring "option_start" "optionStart" .number,
   ring "option_end_skill" "optionEnd" .number,
   ring "option_end_duration" "optionEndDuration" .number,
   ring "option_end_reason" "optionEndReason" .number,
   ring "option_elapsed" "optionElapsed" .number,
   ring "lifetime_reward_sum" "lifeRewardSum" .number,
   ring "lifetime_reward_count" "lifeRewardCount" .number,
   ring "lifetime_reward_family_sum" "lifeRewardFamilySum" (.values [.goalFamilies]),
   ring "lifetime_reward_family_count" "lifeRewardFamilyCount" (.values [.goalFamilies]),
   ring "lifetime_error_sum" "lifeErrorSum" .sum,
   ring "lifetime_error_count" "lifeErrorCount" .sum,
   ring "lifetime_error_count" "lifeErrorCountD" (.values [.demons]),
   ring "settled_return" "settledReturn" (.values [.demons]),
   ring "settled_error" "settledError" (.values [.demons]),
   ring "lifetime_option_started" "lifeOptStarted" (.values [.skills]),
   ring "lifetime_option_completed" "lifeOptCompleted" (.values [.skills]),
   ring "lifetime_option_duration" "lifeOptDuration" (.values [.skills]),
   ring "lifetime_option_end_reasons" "lifeOptEndReasons" (.values [.skills, .optionEnds]),
   ring "lifetime_goal_attempts" "lifeGoalAttempts" (.values [.goalFamilies]),
   ring "lifetime_goal_successes" "lifeGoalSuccesses" (.values [.goalFamilies]),
   ring "lifetime_goal_steps" "lifeGoalSteps" (.values [.goalFamilies]),
   ring "lifetime_cycle_attempts" "cycleAttempts" .cycleBin,
   ring "lifetime_cycle_successes" "cycleSuccesses" .cycleBin,
   ring "lifetime_cycle_steps" "cycleSteps" .cycleBin,
   ring "control_criterion" "criterion" .number,
   ring "retire_step" "retireStep" .number, ring "retire_unit" "retireUnit" .number,
   ring "retire_count" "retireCount" .number,
   ring "subtask_unit" "subtaskUnit" (.values [.skills]),
   ring "subtask_bonus" "subtaskBonus" (.values [.skills]),
   ring "demons" "dem" (.values [.demons]), ring "cums" "cum" (.values [.demons])]

def browserIntakeColumns : List String := ["runStart"]

theorem browserColumns_live :
    ∀ entry ∈ browserColumns, ∃ shape,
      (entry.1, shape) ∈ browserSchema ∧ BrowserColumn.fits entry.1 entry.2 shape = true :=
  schemaCovers_sound BrowserColumn.fits browserColumns browserSchema (by decide +kernel)

theorem browserColumns_distinct :
    (browserColumns.map (·.2.name) ++ browserIntakeColumns ++ ["id", "i"]).Nodup :=
  nodup_of_distinct_keys stringSortKey
    (browserColumns.map (·.2.name) ++ browserIntakeColumns ++ ["id", "i"])
    (by decide +kernel)

end Acorn.Host.Viewer
