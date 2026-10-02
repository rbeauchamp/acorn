/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.CoreTelemetry
import Acorn.Host.Viewer.ControlTelemetry

/-!
# Browser schema linked to the executing emitter

The kernel checks the schema against every native capture, independently of
configuration, state and terminal status. The executable schema is retained as
closed data so the browser requires no initialized agent or world. Whole-frame,
envelope, control and map admission are emitted from it and from the closed
refinements below; `Acorn.Host.Viewer.BrowserRecord` and
`Acorn.Host.Viewer.BrowserStore` derive the page's record and frame store from
the same list.
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

/-- Why the page refuses a whole frame: a closed set, each member with one page counter
and one remedy in the stream-health readout. -/
inductive BrowserRefusal where
  /-- `schema_version` is not the one this page reads: the page and the core were built
  from different trees. -/
  | schema
  /-- A fixed count or an array length disagrees with the schema: the same build skew,
  seen in a shape. -/
  | cardinality
  /-- A required key is absent: a source defect that rebuilding does not fix. -/
  | missingField
  /-- A key is present without the value its schema promises: the emitter or the
  transport is wrong. -/
  | malformed

/-- Wire spelling of a refusal, also the page's counter key. -/
def BrowserRefusal.tag : BrowserRefusal → String
  | .schema => "schema" | .cardinality => "cardinality"
  | .missingField => "missingField" | .malformed => "malformed"

/-- Every refusal reason; the page keeps one counter per member. -/
def BrowserRefusal.all : List BrowserRefusal :=
  [.schema, .cardinality, .missingField, .malformed]

/-- No refusal reason lacks a page counter. -/
theorem BrowserRefusal.all_complete (refusal : BrowserRefusal) :
    refusal ∈ BrowserRefusal.all := by
  cases refusal <;> simp [BrowserRefusal.all]

/-- The page's refusal vocabulary, emitted from the reasons admission returns. -/
def browserRefusalJavascript : String :=
  "const Reject=Object.freeze({" ++
    String.intercalate "," (BrowserRefusal.all.map fun refusal =>
      refusal.tag ++ ":" ++ telemetryString refusal.tag) ++ "});\n"

private def refuse (why : BrowserRefusal) (key : String) : String :=
  "return {why:" ++ telemetryString why.tag ++ ",key:" ++ telemetryString key ++ "};\n"

/-- Generated whole-record admission returns the refused wire key and reason.
The native emitter/schema equality owns structural coverage; refinements own
the browser projection domain. Unknown fields remain forward-compatible. -/
def browserAdmissionJavascript : String :=
  "function observerAdmission(f){\nif(!f||typeof f!=='object'||Array.isArray(f))" ++
    refuse .malformed "frame" ++
  String.join (browserSchema.map fun (key, shape) =>
    let access := "f[" ++ telemetryString key ++ "]"
    let cardinality := match shape with
      | .array count _ => s!"if(Array.isArray({access})&&{access}.length!=={count})" ++
          refuse .cardinality key
      | _ => ""
    "if(!Object.hasOwn(f," ++ telemetryString key ++ "))" ++ refuse .missingField key ++
      cardinality ++ "if(!" ++ shape.browserPredicate access ++ ")" ++ refuse .malformed key) ++
  String.join (browserRules.map fun (key, rule) =>
    let why : BrowserRefusal := match rule with
      | .exact _ => if key == "schema_version" then .schema else .cardinality
      | _ => .malformed
    "if(!" ++ rule.javascript ("f[" ++ telemetryString key ++ "]") ++ ")" ++ refuse why key) ++
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
   ("actual", .tags (Phase.representatives.map Phase.controlTag)),
   ("desired", .tags ["running", "stopped"]), ("seed", .shape .natural),
   ("checkpointRefused", .shape .flag), ("clearDisabled", .shape (.optional .text)),
   ("terminalWarning", .shape (.optional .text)),
   ("tail", .list 6 (.shape .text))]

/-- Retained map header admission precedes browser storage or painting. -/
def browserMapRules : List (String × BrowserRule) :=
  [("runId", .hex 16), ("side", .shape .natural), ("side", .positive), ("side", .range 4097),
   ("seed", .shape .natural), ("kinds", .shape .text), ("partial", .shape .flag)]

/-- Envelope, control and map admission, each independent of whole-frame admission. -/
def browserRulesJavascript : String :=
  rulesFunction "observerEnvelope" browserEnvelopeRules ++
    rulesFunction "observerControl" browserControlRules ++
    rulesFunction "observerMap" browserMapRules

end Acorn.Host.Viewer
