/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.BrowserRecord
import Acorn.Host.Viewer.WorldMemory

/-!
# Page constants and frame store derived from the browser schema

The page's named dimensions are emitted from their Lean owners. The frame ring
is one table of columns, each reading one record field: allocation, the write
of a record into a slot and the view that reads a slot back are all emitted
from that table, and no two of its properties share a name
(`browserColumns_distinct`), so an encoding and its inverse cannot differ. The
binding of a store to its capacity, with the slot of a frame id, is emitted too.
Each column's key is a schema key whose record value its encoding is defined
for, and each symbolic stride equals the schema's array width.

Typed-array assignment and this structural emitter remain trusted execution
boundaries. The page's painters index the array columns with the same named
dimensions; that use is hand-written.
-/
namespace Acorn.Host.Viewer

/-- A named page dimension, emitted from its Lean owner. -/
inductive BrowserConstant where
  /-- Telemetry schema version this page reads. -/
  | schema
  /-- Byte of a map cell never sensed. The stream's absent-option code is the same
  value (`BrowserConstant.unseen_admitted`), and the page compares option slots with
  this name too. -/
  | unseen
  /-- Largest world side the viewer server retains a map for. -/
  | mapSide
  /-- Terrain kinds. -/
  | tileKinds
  /-- Prediction questions (demons). -/
  | demons
  /-- Primitive actions. -/
  | primitives
  /-- Meta-controller actions: the primitive hand-off and one per option slot. -/
  | metaActions
  /-- Tiles of the sensed patch. -/
  | patch
  /-- Option slots. -/
  | skills
  /-- Option ending reasons. -/
  | optionEnds
  /-- Goal families. -/
  | goalFamilies
  /-- Learned model heads per option slot. -/
  | modelHeads
  /-- Lifetime history bins. -/
  | historyBins
  /-- Curriculum-cycle bins. -/
  | cycleBins
  /-- Curriculum cycles that own an exact bin. -/
  | exactCycles

/-- The JavaScript name the page reads. -/
def BrowserConstant.name : BrowserConstant → String
  | .schema => "SCHEMA" | .unseen => "UNSEEN" | .mapSide => "MAX_MAP_SIDE"
  | .tileKinds => "N_KIND" | .demons => "N_DEM" | .primitives => "N_CTL"
  | .metaActions => "N_META" | .patch => "N_TILE" | .skills => "N_SKILL"
  | .optionEnds => "N_OPTION_END" | .goalFamilies => "N_GOAL_FAMILY"
  | .modelHeads => "N_MODEL" | .historyBins => "HISTORY_BINS"
  | .cycleBins => "CYCLE_BINS" | .exactCycles => "EXACT_CYCLES"

/-- The owner's value. Three literal dimensions (`optionEnds`, `goalFamilies` and
`modelHeads`) are held to the schema's array widths by `browserColumns_live`, and the
kind count to admission by `BrowserConstant.tileKinds_admitted`. -/
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

/-- Every named dimension, in emission order. -/
def BrowserConstant.all : List BrowserConstant :=
  [.schema, .unseen, .mapSide, .tileKinds, .demons, .primitives, .metaActions, .patch,
   .skills, .optionEnds, .goalFamilies, .modelHeads, .historyBins, .cycleBins, .exactCycles]

/-- No named dimension is left undeclared on the page. -/
theorem BrowserConstant.all_complete (constant : BrowserConstant) :
    constant ∈ BrowserConstant.all := by
  cases constant <;> simp [BrowserConstant.all]

/-- A meta action is the primitive hand-off or exactly one option slot. -/
theorem BrowserConstant.metaActions_skills :
    BrowserConstant.metaActions.value = BrowserConstant.skills.value + 1 := by
  decide

/-- The page's named dimensions, declared once. -/
def browserConstantsJavascript : String :=
  "const " ++ String.intercalate "," (BrowserConstant.all.map fun constant =>
    constant.name ++ "=" ++ toString constant.value) ++ ";\n"

/-- The width a symbolic stride denotes. -/
def BrowserConstant.product (stride : List BrowserConstant) : Nat :=
  stride.foldl (fun width constant => width * constant.value) 1

/-- Closed spellings admission holds a text field to; empty when it declares none. -/
def browserTags (key : String) : List String :=
  (browserRules.findSome? fun (name, rule) =>
    match rule with
    | .tags values => if name = key then some values else none
    | _ => none).getD []

/-- Exclusive bound admission places on each element of an array field. -/
def browserElementBound (key : String) : Option Nat :=
  browserRules.findSome? fun (name, rule) =>
    match rule with
    | .each (.range upper) => if name = key then some upper else none
    | _ => none

/-- The emitted kind count is the bound admission holds every sensed tile below. -/
theorem BrowserConstant.tileKinds_admitted :
    browserElementBound "tiles" = some BrowserConstant.tileKinds.value := by
  decide +kernel

/-- Each field admission lets carry an index or one code for "none", with that code. -/
def browserAbsentCodes : List (String × Nat) :=
  browserRules.filterMap fun (key, rule) =>
    match rule with
    | .either _ (.exact code) => some (key, code)
    | _ => none

/-- The fields admitted with an absent code are the option fields, and the code of
each is the emitted unseen byte. -/
theorem BrowserConstant.unseen_admitted :
    browserAbsentCodes =
      ["skill", "option_start", "option_end_skill", "option_end_reason", "meta_action"].map
        fun key => (key, BrowserConstant.unseen.value) := by
  decide +kernel

/-- How a ring column holds one record field. -/
inductive BrowserEncoding where
  /-- One number per frame. -/
  | number
  /-- A flag as 0 or 1, read back as a boolean. -/
  | flag
  /-- A closed spelling as its index in the admitted vocabulary, read back as the
  spelling. -/
  | tag
  /-- The ordered sum of a numeric array. -/
  | sum
  /-- A text value, kept as it is. -/
  | text
  /-- A numeric array at a symbolic stride. -/
  | values (stride : List BrowserConstant)
  /-- An array of admitted bytes at a symbolic stride. -/
  | bytes (stride : List BrowserConstant)
  /-- Per goal family, the lifetime bin of the frame's own curriculum cycle. -/
  | cycleBin

/-- One column of the frame ring. -/
structure BrowserColumn where
  /-- Property of the store, and of the frame view for a scalar encoding. -/
  name : String
  /-- How the column holds its record field. -/
  encoding : BrowserEncoding

/-- The record field whose bin selects a `cycleBin` column's values. -/
def browserCycleKey : String := "cycle"

/-- The cycle whose bin is stored is itself an admitted natural. -/
theorem browserCycleKey_admitted :
    (browserCycleKey, TelemetryShape.natural) ∈ browserSchema := by
  decide +kernel

/-- The record values an encoding is defined for: a number, a flag, a text with a
declared vocabulary, or a numeric array whose length is the symbolic stride. A byte
column additionally needs admission to bound each element by a byte. -/
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

/-- The frame ring, by wire key in schema order. -/
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

/-- Number columns that frame intake writes after the record, outside this table. -/
def browserIntakeColumns : List String := ["runStart"]

/-- Every ring column reads a schema key whose record value its encoding is defined
for. In particular each symbolic stride equals the schema's array width, each tagged
field has a declared vocabulary and each byte column holds admitted bytes. -/
theorem browserColumns_live :
    ∀ entry ∈ browserColumns, ∃ shape,
      (entry.1, shape) ∈ browserSchema ∧ BrowserColumn.fits entry.1 entry.2 shape = true :=
  schemaCovers_sound BrowserColumn.fits browserColumns browserSchema (by decide +kernel)

/-- No two properties of the store or of the frame view share a name, so each column's
allocation, write and view address storage of its own. -/
theorem browserColumns_distinct :
    (browserColumns.map (·.2.name) ++ browserIntakeColumns ++ ["id", "i"]).Nodup := by
  decide +kernel

private def scaled (base : String) (stride : List BrowserConstant) : String :=
  String.intercalate "*" (base :: stride.map BrowserConstant.name)

private def tagList (key : String) : String :=
  "[" ++ String.intercalate "," ((browserTags key).map telemetryString) ++ "]"

/-- One property of the store object: every number column has the single binary64
representation, which holds each safe integer and widened binary32 value exactly. -/
def BrowserColumn.allocation (column : BrowserColumn) : String :=
  let storage := match column.encoding with
    | .number | .flag | .tag | .sum => "new Float64Array(CAP)"
    | .text => "new Array(CAP)"
    | .values stride => "new Float64Array(" ++ scaled "CAP" stride ++ ")"
    | .bytes stride => "new Uint8Array(" ++ scaled "CAP" stride ++ ")"
    | .cycleBin => "new Float64Array(" ++ scaled "CAP" [.goalFamilies] ++ ")"
  "  " ++ column.name ++ ":" ++ storage ++ ",\n"

/-- The write of record `f` into slot `i` of store `S`. -/
def BrowserColumn.write (key : String) (column : BrowserColumn) : String :=
  let value := "f[" ++ telemetryString key ++ "]"
  let cell := "S." ++ column.name ++ "[i]"
  let statement := match column.encoding with
    | .number | .text => cell ++ "=" ++ value ++ ";"
    | .flag => cell ++ "=" ++ value ++ "?1:0;"
    | .tag => cell ++ "=" ++ tagList key ++ ".indexOf(" ++ value ++ ");"
    | .sum => cell ++ "=observerSum(" ++ value ++ ");"
    | .values stride | .bytes stride =>
      "S." ++ column.name ++ ".set(" ++ value ++ "," ++ scaled "i" stride ++ ");"
    | .cycleBin =>
      let families := BrowserConstant.goalFamilies.name
      "for(let k=0;k<" ++ families ++ ";k++)S." ++ column.name ++ "[i*" ++ families ++
        "+k]=" ++ value ++ "[k*" ++ BrowserConstant.cycleBins.name ++ "+b];"
  statement ++ "\n"

/-- The frame-view property that reads slot `i` back, for a scalar encoding. -/
def BrowserColumn.view (key : String) (column : BrowserColumn) : Option String :=
  let cell := "S." ++ column.name ++ "[i]"
  match column.encoding with
  | .number | .sum | .text => some (column.name ++ ":" ++ cell)
  | .flag => some (column.name ++ ":!!" ++ cell)
  | .tag => some (column.name ++ ":" ++ tagList key ++ "[" ++ cell ++ "]")
  | .values _ | .bytes _ | .cycleBin => none

/-- Allocation, record write and frame view of the ring, from the one column table.
The write stores the lifetime bin of the frame's own cycle, selected by the generated
`observerCycleBucket`; `observerSum` is the page's adapter over the generated sum.
`observerRing` binds one store to its capacity: its `store` and `frame` are the
generated write and view at `slot(id)`. -/
def browserStoreJavascript : String :=
  "function observerFrameStore(CAP){return {\n" ++
  String.join (browserColumns.map fun (_, column) => column.allocation) ++
  String.join (browserIntakeColumns.map fun name =>
    "  " ++ name ++ ":new Float64Array(CAP),\n") ++
  "};}\n" ++
  "function observerStore(S,i,f){\nconst b=observerCycleBucket(f[" ++
    telemetryString browserCycleKey ++ "]);\n" ++
  String.join (browserColumns.map fun (key, column) => column.write key) ++ "}\n" ++
  "function observerFrame(S,id,i){return {id,i,\n" ++
  String.intercalate ",\n" (browserColumns.filterMap fun (key, column) => column.view key) ++
  "};}\n" ++
  "function observerRing(CAP){const S=observerFrameStore(CAP),slot=id=>id%CAP;" ++
  "return {S,slot,store:(id,f)=>observerStore(S,slot(id),f)," ++
  "frame:id=>observerFrame(S,id,slot(id))};}\n"

end Acorn.Host.Viewer
