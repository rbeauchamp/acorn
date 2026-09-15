/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.CoreTelemetry
import Acorn.Host.Viewer.BrowserMath
import Acorn.Host.Viewer.ClockProgram
import Acorn.Host.Viewer.BrowserNat

/-!
# Browser schema linked to the executing emitter

The kernel checks the schema against every native capture, independently of
configuration, state and terminal status. The executable schema is retained as
closed data so the browser requires no initialized agent or world.
-/
namespace Acorn.Host.Viewer
open Features Handcrafted

/-- Closed protocol schema; the universal equality below guards all names and shapes. -/
def browserSchema : List (String × TelemetryShape) :=
  [("schema_version", TelemetryShape.natural), ("source_sha256", TelemetryShape.text),
  ("build_sha256", TelemetryShape.text), ("audit_digest", TelemetryShape.text), ("run_id", TelemetryShape.text),
  ("agent_epoch", TelemetryShape.natural), ("origin", TelemetryShape.text), ("timestamp_ms", TelemetryShape.natural),
  ("update_us", TelemetryShape.natural), ("environment_us", TelemetryShape.natural),
  ("process_uptime_ms", TelemetryShape.natural),
  ("process_started_ms", TelemetryShape.natural), ("core_rss_bytes", TelemetryShape.natural.optional),
  ("checkpoint_bytes", TelemetryShape.natural.optional), ("checkpoint_write_us", TelemetryShape.natural.optional),
  ("checkpoint_failures", TelemetryShape.natural), ("telemetry_refusals", TelemetryShape.natural),
  ("telemetry_drops", TelemetryShape.natural), ("goal_count", TelemetryShape.natural),
  ("attempt_cap", TelemetryShape.natural), ("step_cap", TelemetryShape.natural), ("cycle_cap", TelemetryShape.natural),
  ("goal_progress_invalid", TelemetryShape.flag),
  ("goal_progress_cycle", TelemetryShape.natural),
  ("goal_progress_resolved", TelemetryShape.natural),
  ("goal_progress_attempt", TelemetryShape.natural),
  ("goal_progress_achieved", TelemetryShape.natural),
  ("goal_progress_completed_cycle", TelemetryShape.natural.optional),
  ("goal_progress_completed_achieved", TelemetryShape.natural.optional),
  ("goal_progress_score", TelemetryShape.natural.optional),
  ("curriculum_names", .sequence .text),
  ("curriculum_failed_attempts", .sequence .natural),
  ("curriculum_success_steps", .sequence (.optional .natural)),
  ("world_step", TelemetryShape.natural), ("seed", TelemetryShape.natural), ("side", TelemetryShape.natural),
  ("day_length", TelemetryShape.natural), ("regrow", TelemetryShape.natural), ("food_interval", TelemetryShape.natural),
  ("food_cap", TelemetryShape.natural), ("deer_cap", TelemetryShape.natural), ("x", TelemetryShape.integer),
  ("y", TelemetryShape.integer), ("facing", TelemetryShape.natural), ("energy", TelemetryShape.natural),
  ("wood", TelemetryShape.natural), ("stone", TelemetryShape.natural), ("food", TelemetryShape.natural),
  ("gold", TelemetryShape.natural), ("axe", TelemetryShape.flag), ("boat", TelemetryShape.flag),
  ("action", TelemetryShape.natural), ("reward", TelemetryShape.binary32), ("done", TelemetryShape.flag),
  ("ev", TelemetryShape.natural), ("goal", TelemetryShape.natural), ("attempt", TelemetryShape.natural),
  ("tier", TelemetryShape.natural), ("cycle", TelemetryShape.natural), ("gkind", TelemetryShape.goalKind),
  ("gitem", TelemetryShape.goalItem), ("gx", TelemetryShape.integer), ("gy", TelemetryShape.integer),
  ("gn", TelemetryShape.natural), ("tiles", TelemetryShape.array 121 TelemetryShape.natural),
  ("tile_extra", TelemetryShape.array 121 TelemetryShape.natural), ("end", TelemetryShape.flag),
  ("lifetime_step", TelemetryShape.natural), ("reward_rate", TelemetryShape.binary32), ("eps", TelemetryShape.binary32),
  ("mean_alpha", TelemetryShape.binary32), ("a_ctl", TelemetryShape.binary32), ("a_dem", TelemetryShape.binary32),
  ("alpha_control_all", TelemetryShape.array 9 TelemetryShape.binary32),
  ("alpha_meta_all", TelemetryShape.array 4 TelemetryShape.binary32),
  ("alpha_option_all", TelemetryShape.array 27 TelemetryShape.binary32),
  ("alpha_demon_all", TelemetryShape.array 11 TelemetryShape.binary32),
  ("alpha_models", TelemetryShape.array 9 TelemetryShape.binary32),
  ("credit_control", TelemetryShape.array 9 TelemetryShape.natural),
  ("credit_meta", TelemetryShape.array 4 TelemetryShape.natural),
  ("credit_options", TelemetryShape.array 27 TelemetryShape.natural),
  ("credit_demons", TelemetryShape.array 11 TelemetryShape.natural),
  ("credit_models", TelemetryShape.array 9 TelemetryShape.natural),
  ("option_model_rewards", TelemetryShape.array 3 TelemetryShape.binary32),
  ("option_model_continuations", TelemetryShape.array 3 TelemetryShape.binary32),
  ("option_model_durations", TelemetryShape.array 3 TelemetryShape.binary32),
  ("planning_errors", TelemetryShape.array 3 TelemetryShape.binary32), ("planning_steps", TelemetryShape.natural),
  ("decision_source", TelemetryShape.text), ("skill", TelemetryShape.natural), ("explored", TelemetryShape.flag),
  ("control", TelemetryShape.array 9 TelemetryShape.binary32), ("meta", TelemetryShape.array 4 TelemetryShape.binary32),
  ("action_probabilities", TelemetryShape.array 9 TelemetryShape.binary32),
  ("meta_probabilities", TelemetryShape.array 4 TelemetryShape.binary32), ("meta_action", TelemetryShape.natural),
  ("option_start", TelemetryShape.natural), ("option_end_skill", TelemetryShape.natural),
  ("option_end_duration", TelemetryShape.natural), ("option_end_reason", TelemetryShape.natural),
  ("option_elapsed", TelemetryShape.natural), ("lifetime_reward_sum", TelemetryShape.binary64),
  ("lifetime_reward_count", TelemetryShape.natural),
  ("lifetime_reward_family_sum", TelemetryShape.array 4 TelemetryShape.binary64),
  ("lifetime_reward_family_count", TelemetryShape.array 4 TelemetryShape.natural),
  ("lifetime_reward_history_sum", TelemetryShape.array 64 TelemetryShape.binary64),
  ("lifetime_reward_history_count", TelemetryShape.array 64 TelemetryShape.natural),
  ("lifetime_error_history_sum", TelemetryShape.array 64 TelemetryShape.binary64),
  ("lifetime_error_history_count", TelemetryShape.array 64 TelemetryShape.natural),
  ("lifetime_error_sum", TelemetryShape.array 11 TelemetryShape.binary64),
  ("lifetime_error_count", TelemetryShape.array 11 TelemetryShape.natural),
  ("settled_return", TelemetryShape.array 11 TelemetryShape.binary32),
  ("settled_error", TelemetryShape.array 11 TelemetryShape.binary32),
  ("lifetime_option_started", TelemetryShape.array 3 TelemetryShape.natural),
  ("lifetime_option_completed", TelemetryShape.array 3 TelemetryShape.natural),
  ("lifetime_option_duration", TelemetryShape.array 3 TelemetryShape.natural),
  ("lifetime_option_end_reasons", TelemetryShape.array 9 TelemetryShape.natural),
  ("lifetime_goal_attempts", TelemetryShape.array 4 TelemetryShape.natural),
  ("lifetime_goal_successes", TelemetryShape.array 4 TelemetryShape.natural),
  ("lifetime_goal_steps", TelemetryShape.array 4 TelemetryShape.natural),
  ("lifetime_cycle_attempts", TelemetryShape.array 64 TelemetryShape.natural),
  ("lifetime_cycle_successes", TelemetryShape.array 64 TelemetryShape.natural),
  ("lifetime_cycle_steps", TelemetryShape.array 64 TelemetryShape.natural),
  ("agreement_version", TelemetryShape.natural),
  ("agreement_scale", TelemetryShape.natural),
  ("agreement_started", TelemetryShape.natural.optional),
  ("agreement_stopped", TelemetryShape.flag),
  ("agreement_score", TelemetryShape.natural.optional),
  ("agreement_text", TelemetryShape.text.optional),
  ("agreement_error", TelemetryShape.natural.optional),
  ("agreement_channel_score", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_channel_text", .array demonLayout.length (TelemetryShape.text.optional)),
  ("agreement_channel_error", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_count", .array demonLayout.length (TelemetryShape.text)),
  ("agreement_pending", .array demonLayout.length (TelemetryShape.natural)),
  ("agreement_censored", .array demonLayout.length (TelemetryShape.text)),
  ("agreement_status", .array demonLayout.length (TelemetryShape.text)),
  ("agreement_horizon", .array demonLayout.length (TelemetryShape.natural)),
  ("agreement_start_first", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_start_last", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_settlement_first", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_settlement_last", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_tail", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_rounding", .array demonLayout.length (TelemetryShape.natural.optional)),
  ("agreement_history_clock", .array FeatureConstants.historyBins (TelemetryShape.natural.optional)),
  ("agreement_history_score", .array FeatureConstants.historyBins (TelemetryShape.natural.optional)),
  ("checkpoint_format", TelemetryShape.natural), ("control_criterion", TelemetryShape.natural),
  ("weight_space", TelemetryShape.natural), ("primitive_count", TelemetryShape.natural),
  ("meta_count", TelemetryShape.natural), ("skill_count", TelemetryShape.natural),
  ("option_end_count", TelemetryShape.natural), ("demon_count", TelemetryShape.natural),
  ("learner_count", TelemetryShape.natural), ("history_bins", TelemetryShape.natural),
  ("cycle_bins", TelemetryShape.natural), ("exact_cycles", TelemetryShape.natural),
  ("settle_stride", TelemetryShape.natural), ("settle_remaining", TelemetryShape.binary32),
  ("n_tilings", TelemetryShape.natural), ("imprint_units", TelemetryShape.natural),
  ("retire_step", TelemetryShape.natural.optional), ("retire_unit", TelemetryShape.natural.optional),
  ("retire_count", TelemetryShape.natural), ("subtask_policy", TelemetryShape.text),
  ("subtask_unit", TelemetryShape.array 3 TelemetryShape.natural.optional),
  ("subtask_bonus", TelemetryShape.array 3 TelemetryShape.binary32),
  ("action_names", TelemetryShape.array 9 TelemetryShape.text),
  ("meta_names", TelemetryShape.array 4 TelemetryShape.text),
  ("skill_names", TelemetryShape.array 3 TelemetryShape.text),
  ("goal_family_names", TelemetryShape.array 4 TelemetryShape.text),
  ("demons", TelemetryShape.array 11 TelemetryShape.binary32),
  ("cums", TelemetryShape.array 11 TelemetryShape.binary32),
  ("demon_names", TelemetryShape.array 11 TelemetryShape.text),
  ("demon_target_policy", TelemetryShape.array 11 TelemetryShape.text),
  ("demon_gamma", TelemetryShape.array 11 TelemetryShape.binary32),
  ("demon_horizon", TelemetryShape.array 11 TelemetryShape.binary32)]

set_option maxRecDepth 4096 in
/-- Every emitted capture has precisely the browser's admitted structural schema. -/
theorem browserSchema_execution {config : Features.Config} {dimension : Dimension}
    (context : TelemetryContext) (frame : StepFrame (AgentObservation config dimension))
    (terminal : Bool) : telemetrySchema (coreTelemetry context frame terminal) = browserSchema := by
  rfl

/-- Structural backend for one wire shape. JavaScript parsing, binary64 numeric
admission and array iteration are the declared browser runtime primitives. -/
def TelemetryShape.browserPredicate : TelemetryShape → String → String
  | .natural, x => s!"(Number.isSafeInteger({x})&&{x}>=0)"
  | .goalKind, x =>
    "[" ++ String.intercalate "," (goalKindCodes.map toString) ++ s!"].includes({x})"
  | .goalItem, x =>
    "[" ++ String.intercalate "," (goalItemCodes.map toString) ++ s!"].includes({x})"
  | .integer, x => s!"Number.isSafeInteger({x})"
  | .binary32, x =>
    s!"({x}===null||(typeof {x}==='number'&&Number.isFinite({x})&&Number.isFinite(Math.fround({x}))))"
  | .binary64, x =>
    s!"({x}===null||(typeof {x}==='number'&&Number.isFinite({x})))"
  | .flag, x => s!"(typeof {x}==='boolean')"
  | .text, x => s!"(typeof {x}==='string')"
  | .optional element, x => "(" ++ x ++ "===null||" ++ element.browserPredicate x ++ ")"
  | .array count element, x =>
    s!"(Array.isArray({x})&&{x}.length==={count}&&{x}.every(v=>" ++
      element.browserPredicate "v" ++ "))"

  | .sequence element, x =>
    s!"(Array.isArray({x})&&{x}.every(v=>" ++ element.browserPredicate "v" ++ "))"

/-- Closed refinements beyond structural JSON shapes. -/
inductive BrowserRule where
  /-- A structural wire value. -/
  | shape (value : TelemetryShape)
  /-- Equality to a declared integer protocol constant. -/
  | exact (value : Nat)
  /-- One of the owner's closed spellings. -/
  | tags (values : List String)
  /-- Fixed-width lowercase hexadecimal. -/
  | hex (width : Nat)
  /-- Present indices are strictly below the named dimension. -/
  | belowField (field : String)
  /-- Present counters do not exceed the named clock. -/
  | atMost (field : String)
  /-- Sequence length equals the admitted population field. -/
  | lengthField (field : String)
  /-- Apply a refinement to every array element. -/
  | each (rule : BrowserRule)
  /-- Closed half-open numeric range. -/
  | range (upper : Nat)
  /-- Explicit null absence is permitted. -/
  | nullable (rule : BrowserRule)
  /-- Bounded variable-length list. -/
  | list (maximum : Nat) (element : BrowserRule)
  /-- Union of two admitted refinements. -/
  | either (left right : BrowserRule)
  /-- Strict positivity after structural numeric admission. -/
  | positive
  /-- Canonical decimal text retains an exact bounded counter beyond binary64 integers. -/
  | decimal (maximum : Nat)

/-- Structural refinement backend; field keys and tag values are JSON-escaped. -/
def BrowserRule.javascript : BrowserRule → String → String
  | .shape schemaValue, x => schemaValue.browserPredicate x
  | .exact value, x => s!"({x}==={value})"
  | .tags values, x =>
    "[" ++ String.intercalate "," (values.map telemetryString) ++ s!"].includes({x})"
  | .hex width, x => s!"(typeof {x}==='string'&&{x}.length==={width}&&/^[0-9a-f]+$/.test({x}))"
  | .belowField field, x => s!"({x}===null||{x}<f[" ++ telemetryString field ++ "])"
  | .atMost field, x => s!"({x}===null||{x}<=f[" ++ telemetryString field ++ "])"
  | .lengthField field, x => s!"({x}.length===f[" ++ telemetryString field ++ "])"
  | .each rule, x => s!"{x}.every(v=>" ++ rule.javascript "v" ++ ")"
  | .range upper, x => s!"({x}>=0&&{x}<{upper})"
  | .nullable rule, x => s!"({x}===null||" ++ rule.javascript x ++ ")"
  | .list maximum rule, x => s!"(Array.isArray({x})&&{x}.length<={maximum}&&{x}.every(v=>" ++
      rule.javascript "v" ++ "))"
  | .either left right, x => "(" ++ left.javascript x ++ "||" ++ right.javascript x ++ ")"
  | .positive, x => s!"({x}>0)"
  | .decimal maximum, x =>
    s!"(typeof {x}==='string'&&{x}.length<={toString maximum |>.length}&&" ++
      s!"/^(0|[1-9][0-9]*)$/.test({x})&&BigInt({x})<=BigInt('{maximum}'))"

/-- Refinements retain current protocol constants and state-relative index bounds. -/
def browserRules : List (String × BrowserRule) :=
  [("curriculum_names", .lengthField "goal_count"),
   ("curriculum_failed_attempts", .lengthField "goal_count"),
   ("curriculum_success_steps", .lengthField "goal_count"),
   ("curriculum_failed_attempts", .each (.atMost "attempt_cap")),
   ("curriculum_success_steps", .each (.atMost "step_cap"))] ++
  [("schema_version", .exact telemetrySchemaVersion),
   ("goal_progress_score", .nullable (.range 1001)),
   ("goal_progress_resolved", .atMost "goal_count"),
    ("goal_progress_attempt", .atMost "attempt_cap"),
   ("goal_progress_achieved", .atMost "goal_progress_resolved"),
   ("goal_progress_completed_achieved", .atMost "goal_count"),
   ("goal_progress_completed_cycle", .atMost "goal_progress_cycle"),
   ("agreement_version", .exact 1),
   ("agreement_scale", .exact Agreement.displayScale),
   ("agreement_score", .nullable (.range (Agreement.displayScale + 1))),
   ("agreement_error", .nullable (.range (Agreement.displayScale + 1))),
   ("agreement_channel_score", .each (.nullable (.range (Agreement.displayScale + 1)))),
   ("agreement_channel_error", .each (.nullable (.range (Agreement.displayScale + 1)))),
   ("agreement_pending", .each (.range (FeatureConstants.pendingSamples + 1))),
   ("agreement_count", .each (.decimal Agreement.countLimit)),
   ("agreement_censored", .each (.decimal Agreement.countLimit)),
   ("agreement_horizon", .each (.range (FeatureConstants.maxSettlement + 1))),
   ("agreement_tail", .each (.nullable (.range (Agreement.displayScale + 1)))),
   ("agreement_rounding", .each (.nullable (.range (Agreement.displayScale + 1)))),
   ("agreement_history_score", .each (.nullable (.range (Agreement.displayScale + 1)))),
   ("agreement_status", .each (.tags
     ["invalid", "saturated", "partially censored", "censored", "pending", "complete", "empty"])),
   ("primitive_count", .exact FeatureConstants.primitiveCount),
   ("meta_count", .exact FeatureConstants.metaActionCount),
   ("skill_count", .exact FeatureConstants.skillCount),
   ("demon_count", .exact FeatureConstants.demonCount),
   ("option_end_count", .exact 3),
   ("history_bins", .exact FeatureConstants.historyBins),
   ("cycle_bins", .exact FeatureConstants.cycleBins),
   ("exact_cycles", .exact FeatureConstants.exactCycles),
   ("learner_count", .exact telemetryLearnerCount),
   ("control_criterion", .range 2),
   ("action", .range FeatureConstants.primitiveCount), ("facing", .range 4),
   ("skill", .either (.range FeatureConstants.skillCount) (.exact 255)),
   ("option_start", .either (.range FeatureConstants.skillCount) (.exact 255)),
   ("option_end_skill", .either (.range FeatureConstants.skillCount) (.exact 255)),
   ("option_end_reason", .either (.range 3) (.exact 255)),
   ("meta_action", .either (.range FeatureConstants.metaActionCount) (.exact 255)),
   ("ev", .range 64), ("side", .positive),
   ("run_id", .hex 16), ("audit_digest", .hex 16),
   ("source_sha256", .hex 64), ("build_sha256", .hex 64),
   ("origin", .tags ["fresh", "resumed", "cleared"]),
   ("decision_source", .tags ["primitive", "exploration_start", "exploration_continuation", "option"]),
   ("subtask_policy", .tags ["learned", "hand_authored"]),
   ("subtask_unit", .each (.belowField "imprint_units")),
   ("subtask_unit", .each (.nullable (.range (2 ^ 31)))),
   ("retire_unit", .belowField "imprint_units"), ("retire_step", .atMost "lifetime_step"),
   ("tiles", .each (.range 8)), ("tile_extra", .each (.range 256))]

/-- Semantic goal fields cannot acquire a second, independently narrowed domain.
Changing the refinement list must preserve this compiler-checked separation. -/
theorem browserRules_goal_separation :
    ∀ entry ∈ browserRules, entry.1 ≠ "gkind" ∧ entry.1 ≠ "gitem" := by
  decide

/-- Item labels are generated from the same exhaustive semantic vocabulary as admission. -/
def browserGoalLabelsJavascript : String :=
  "function observerGoalItemLabel(code,count=1){const labels=({" ++
    String.intercalate "," (goalItems.map fun item =>
      toString item.code ++ ":[" ++ telemetryString item.labels.1 ++ "," ++
        telemetryString item.labels.2 ++ "]") ++
    "})[code];return labels?.[count===1?0:1]??'—';}\n"

private def goalTextExpression : GoalKind → String
  | none => "'—'"
  | some .reach => "'Go to the gold target ('+gx+', '+gy+')'"
  | some .collect => "'Hold at least '+gn+' '+observerGoalItemLabel(gitem,gn).toLowerCase()"
  | some .craft => "'Own '+observerGoalItemLabel(gitem)"
  | some .survive => "'Continue for '+gn+' world steps in this attempt'"

/-- Goal text dispatch is exhaustive over the same family vocabulary as emission. -/
def browserGoalTextJavascript : String :=
  "function observerGoalText(gkind,gitem,gx,gy,gn){switch(gkind){" ++
    String.join (goalKinds.map fun kind =>
      "case " ++ toString kind.code ++ ":return " ++ goalTextExpression kind ++ ";") ++
    "default:return '—';}}\n"

/-- Generated whole-record admission returns the refused wire key and reason.
The native emitter/schema equality owns structural coverage; refinements own
the browser projection domain. Unknown fields remain forward-compatible. -/
def browserAdmissionJavascript : String :=
  "function observerAdmission(f){\nif(!f||typeof f!=='object'||Array.isArray(f))" ++
    "return {why:'malformed',key:'frame'};\n" ++
  String.join (browserSchema.map fun (key, shape) =>
    let access := "f[" ++ telemetryString key ++ "]"
    let cardinality := match shape with
      | .array count _ => s!"if(Array.isArray({access})&&{access}.length!=={count})" ++
          "return {why:'cardinality',key:" ++ telemetryString key ++ "};\n"
      | _ => ""
    "if(!Object.hasOwn(f," ++ telemetryString key ++ "))return {why:'missingField',key:" ++
      telemetryString key ++ "};\n" ++ cardinality ++ "if(!" ++ shape.browserPredicate access ++
      ")return {why:'malformed',key:" ++ telemetryString key ++ "};\n") ++
  String.join (browserRules.map fun (key, rule) =>
    let why := match rule with
      | .exact _ => if key == "schema_version" then "schema" else "cardinality"
      | _ => "malformed"
    "if(!" ++ rule.javascript ("f[" ++ telemetryString key ++ "]") ++
      ")return {why:" ++ telemetryString why ++ ",key:" ++ telemetryString key ++ "};\n") ++
  "return null;\n}\n"

private def rulesFunction (name : String) (rules : List (String × BrowserRule)) : String :=
  "function " ++ name ++ "(f){return !!f&&typeof f==='object'&&!Array.isArray(f)&&" ++
    String.intercalate "&&" (rules.map fun (key, rule) =>
      "Object.hasOwn(f," ++ telemetryString key ++ ")&&" ++
        rule.javascript ("f[" ++ telemetryString key ++ "]")) ++ ";}\n"

/-- Health envelope can be admitted independently when complete frame data is refused. -/
def browserEnvelopeRules : List (String × BrowserRule) :=
  [("run_id", .hex 16), ("agent_epoch", .shape .natural),
   ("timestamp_ms", .shape .natural), ("lifetime_step", .shape .natural),
   ("world_step", .shape .natural)]

/-- Required control-plane fields; optional new presentation metadata remains compatible
with the native supervisor. The control source owns lifecycle transitions. -/
def browserControlRules : List (String × BrowserRule) :=
  [("runId", .hex 16), ("agentEpoch", .shape .natural),
   ("transition", .tags ["initialized", "start_requested", "stop_requested", "clear_requested",
     "core_started", "core_stopped", "restart_scheduled", "archiving", "cleared", "failed"]),
   ("transitionReason", .shape .text), ("reason", .shape .text),
   ("actual", .tags ["starting", "running", "stopping", "clearing", "stopped"]),
   ("desired", .tags ["running", "stopped"]), ("seed", .shape .natural),
   ("checkpointRefused", .shape .flag), ("clearDisabled", .shape (.optional .text)),
   ("terminalWarning", .shape (.optional .text)),
   ("tail", .list 6 (.shape .text))]

/-- Retained map header admission precedes browser storage or painting. -/
def browserMapRules : List (String × BrowserRule) :=
  [("runId", .hex 16), ("side", .shape .natural), ("side", .positive), ("side", .range 4097),
   ("seed", .shape .natural), ("kinds", .shape .text), ("partial", .shape .flag)]

/-- Numeric columns have one representation, derived uniformly from their extents.
Safe integers and widened binary32 values fit the browser's binary64 domain.
No per-column storage-width choice exists. JavaScript execution remains trusted. -/
def browserNumberColumns : List (String × List String) :=
  [
    ("CAP", ["worldStep", "lifetimeStep", "agentEpoch", "origin", "x", "y", "facing", "action", "skill", "ev", "flags", "goal", "attempt", "tier", "cycle", "goalCount", "attemptCap", "energy", "wood", "stone", "food", "gold", "reward", "eps", "alpha", "rewardRate", "criterion", "aCtl", "aDem", "updateUs", "environmentUs", "gkind", "gitem", "gx", "gy", "gn", "planningSteps", "retireCount", "retireStep", "retireUnit", "decisionSource", "explored", "metaAction", "optStart", "optEnd", "optEndReason", "optEndDuration", "optElapsed", "lifeRewardSum", "lifeRewardCount", "lifeErrorSum", "lifeErrorCount", "runStart"]),
    ("CAP*N_DEM", ["dem", "cum", "alphaDemons", "creditDemons", "lifeErrorCountD", "settledReturn", "settledError"]),
    ("CAP*N_CTL", ["ctl", "actProb", "alphaControl", "creditControl"]),
    ("CAP*N_META", ["met", "metaProb", "alphaMeta", "creditMeta"]),
    ("CAP*N_SKILL", ["optModRew", "optModCont", "optModDuration", "planningErrors", "subtaskUnit", "subtaskBonus", "lifeOptStarted", "lifeOptCompleted", "lifeOptDuration"]),
    ("CAP*N_CTL*N_SKILL", ["alphaOptions", "creditOptions"]),
    ("CAP*3*N_SKILL", ["alphaModels", "creditModels"]),
    ("CAP*N_SKILL*N_OPTION_END", ["lifeOptEndReasons"]),
    ("CAP*N_GOAL_FAMILY", ["lifeGoalAttempts", "lifeGoalSuccesses", "lifeGoalSteps", "lifeRewardFamilySum", "lifeRewardFamilyCount", "cycleAttempts", "cycleSuccesses", "cycleSteps"])
  ]

/-- Emit every numeric column through the same binary64 allocation constructor. -/
def browserNumberStorageJavascript : String :=
  String.intercalate "\n" (browserNumberColumns.flatMap fun (extent, names) =>
    names.map fun name => s!"  {name}:new Float64Array({extent}),")

/-- Storage and intake share the generated browser kernel. The two byte columns
contain only sensor kind/extra codes bounded by admission; text keeps its identity.
Direct assignments preserve admitted values under JavaScript typed-array semantics. -/
def browserStorageJavascript : String :=
  "function observerFrameStore(CAP,N_DEM,N_CTL,N_META,N_TILE,N_SKILL,N_OPTION_END,N_GOAL_FAMILY){return {\n" ++
  browserNumberStorageJavascript ++ "\n" ++ String.intercalate "\n" [
    "  runId:new Array(CAP),",
    "  tiles:new Uint8Array(CAP*N_TILE), extra:new Uint8Array(CAP*N_TILE),",
    "};}",
    "function observerStore(id, f) {",
    "  const i = slot(id);",
    "  S.worldStep[i]=f.world_step; S.lifetimeStep[i]=f.lifetime_step;",
    "  S.runId[i]=f.runId; S.agentEpoch[i]=f.agent_epoch;",
    "  S.origin[i] = f.origin === \"resumed\" ? 1 : f.origin === \"cleared\" ? 2 : 0;",
    "  S.x[i]=f.x; S.y[i]=f.y; S.facing[i]=f.facing; S.action[i]=f.action;",
    "  S.skill[i]=f.skill; S.ev[i]=f.ev; S.goal[i]=f.goal; S.attempt[i]=f.attempt;",
    "  S.tier[i]=f.tier; S.cycle[i]=f.cycle; S.goalCount[i]=f.goal_count;",
    "  S.attemptCap[i]=f.attempt_cap; S.energy[i]=f.energy; S.wood[i]=f.wood;",
    "  S.stone[i]=f.stone; S.food[i]=f.food;",
    "  S.gold[i]=f.gold; S.reward[i]=f.reward; S.eps[i]=f.eps;",
    "  S.rewardRate[i]=f.reward_rate; S.criterion[i]=f.control_criterion;",
    "  S.alpha[i]=f.mean_alpha; S.aCtl[i]=f.a_ctl; S.aDem[i]=f.a_dem;",
    "  S.updateUs[i]=f.update_us; S.environmentUs[i]=f.environment_us;",
    "  S.gkind[i]=f.gkind; S.gitem[i]=f.gitem;",
    "  S.gx[i]=f.gx; S.gy[i]=f.gy; S.gn[i]=f.gn;",
    "  S.flags[i] = (f.axe?1:0)|(f.boat?2:0)|(f.done?4:0)|(f.end?8:0);",
    "  S.dem.set(f.dem, i*N_DEM);",
    "  S.cum.set(f.cum, i*N_DEM);",
    "  S.ctl.set(f.ctl, i*N_CTL);",
    "  S.met.set(f.met, i*N_META);",
    "  S.actProb.set(f.actProb, i*N_CTL); S.metaProb.set(f.metaProb, i*N_META);",
    "  S.decisionSource[i] = [\"primitive\",\"exploration_start\",\"exploration_continuation\",\"option\"].indexOf(f.decisionSource);",
    "  S.explored[i] = f.explored ? 1 : 0; S.metaAction[i]=f.meta_action;",
    "  S.optStart[i]=f.option_start; S.optEnd[i]=f.option_end_skill;",
    "  S.optEndReason[i]=f.option_end_reason; S.optEndDuration[i]=f.option_end_duration;",
    "  S.optElapsed[i]=f.option_elapsed;",
    "  S.optModRew.set(f.optModRew, i*N_SKILL);",
    "  S.optModCont.set(f.optModCont, i*N_SKILL);",
    "  S.optModDuration.set(f.optModDuration, i*N_SKILL);",
    "  S.planningSteps[i]=f.planning_steps;",
    "  S.planningErrors.set(f.planningErrors, i*N_SKILL);",
    "  S.subtaskUnit.set(f.subtaskUnit, i*N_SKILL); S.subtaskBonus.set(f.subtaskBonus, i*N_SKILL);",
    "  S.retireCount[i]=f.retire_count; S.retireStep[i]=f.retire_step; S.retireUnit[i]=f.retire_unit;",
    "  S.alphaControl.set(f.alphaControl,i*N_CTL); S.alphaMeta.set(f.alphaMeta,i*N_META);",
    "  S.alphaOptions.set(f.alphaOptions,i*N_CTL*N_SKILL); S.alphaDemons.set(f.alphaDemons,i*N_DEM);",
    "  S.alphaModels.set(f.alphaModels,i*3*N_SKILL);",
    "  S.creditControl.set(f.creditControl,i*N_CTL); S.creditMeta.set(f.creditMeta,i*N_META);",
    "  S.creditOptions.set(f.creditOptions,i*N_CTL*N_SKILL); S.creditDemons.set(f.creditDemons,i*N_DEM);",
    "  S.creditModels.set(f.creditModels,i*3*N_SKILL);",
    "  S.lifeRewardSum[i]=f.lifetime_reward_sum; S.lifeRewardCount[i]=f.lifetime_reward_count;",
    "  S.lifeErrorSum[i]=observerSum(f.lifeErrorSum);",
    "  S.lifeErrorCount[i]=observerSum(f.lifeErrorCount);",
    "  S.lifeErrorCountD.set(f.lifeErrorCount,i*N_DEM); S.settledReturn.set(f.settledReturn,i*N_DEM);",
    "  S.settledError.set(f.settledError,i*N_DEM);",
    "  S.lifeOptStarted.set(f.lifeOptStarted,i*N_SKILL);",
    "  S.lifeOptCompleted.set(f.lifeOptCompleted,i*N_SKILL);",
    "  S.lifeOptDuration.set(f.lifeOptDuration,i*N_SKILL);",
    "  S.lifeOptEndReasons.set(f.lifeOptEndReasons,i*N_SKILL*N_OPTION_END);",
    "  S.lifeGoalAttempts.set(f.lifeGoalAttempts,i*N_GOAL_FAMILY);",
    "  S.lifeGoalSuccesses.set(f.lifeGoalSuccesses,i*N_GOAL_FAMILY);",
    "  S.lifeGoalSteps.set(f.lifeGoalSteps,i*N_GOAL_FAMILY);",
    "  S.lifeRewardFamilySum.set(f.lifeRewardFamilySum,i*N_GOAL_FAMILY);",
    "  S.lifeRewardFamilyCount.set(f.lifeRewardFamilyCount,i*N_GOAL_FAMILY);",
    "  const cb=cycleBucket(f.cycle);",
    "  for(let family=0;family<N_GOAL_FAMILY;family++){",
    "    const src=family*CYCLE_BINS+cb,dst=i*N_GOAL_FAMILY+family;",
    "    S.cycleAttempts[dst]=f.lifeCycleAttempts[src];",
    "    S.cycleSuccesses[dst]=f.lifeCycleSuccesses[src];",
    "    S.cycleSteps[dst]=f.lifeCycleSteps[src];",
    "  }",
    "  S.tiles.set(f.tiles, i*N_TILE);",
    "  S.extra.set(f.extra, i*N_TILE);",
    "}",
    ""]

/-- One generated resource owns admission and observer calculations together. -/
def browserKernelJavascript : String :=
  browserStorageJavascript ++ BrowserMath.javascript ++ browserGoalLabelsJavascript ++ browserGoalTextJavascript ++ browserAdmissionJavascript ++ ClockProgram.javascript ++ BrowserNat.javascript ++
    rulesFunction "observerEnvelope" browserEnvelopeRules ++
    rulesFunction "observerControl" browserControlRules ++
    rulesFunction "observerMap" browserMapRules

end Acorn.Host.Viewer
