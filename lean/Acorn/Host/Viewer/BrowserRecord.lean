import Acorn.Host.Viewer.BrowserSchema

namespace Acorn.Host.Viewer

def schemaFrom (key : String) :
    List (String × TelemetryShape) → List (String × TelemetryShape)
  | [] => []
  | (name, shape) :: rest =>
    if name = key then (name, shape) :: rest else schemaFrom key rest

theorem schemaFrom_head (key : String) :
    ∀ (schema : List (String × TelemetryShape)) (name : String) (shape : TelemetryShape)
      (later : List (String × TelemetryShape)),
      schemaFrom key schema = (name, shape) :: later →
      name = key ∧ ∀ entry ∈ (name, shape) :: later, entry ∈ schema
  | [], _, _, _, located => by simp [schemaFrom] at located
  | (first, firstShape) :: rest, name, shape, later, located => by
    by_cases same : first = key
    · simp only [schemaFrom, ite_eq_left same] at located
      cases located
      exact ⟨same, fun _ member => member⟩
    · simp only [schemaFrom, ite_eq_right same] at located
      obtain ⟨named, members⟩ := schemaFrom_head key rest name shape later located
      exact ⟨named, fun entry member => List.mem_cons_of_mem _ (members entry member)⟩

def schemaCovers {α : Type} (fits : String → α → TelemetryShape → Bool) :
    List (String × α) → List (String × TelemetryShape) → Bool
  | [], _ => true
  | (key, item) :: rest, schema =>
    match schemaFrom key schema with
    | [] => false
    | (name, shape) :: later =>
      fits key item shape && schemaCovers fits rest ((name, shape) :: later)

theorem schemaCovers_sound {α : Type} (fits : String → α → TelemetryShape → Bool) :
    ∀ (table : List (String × α)) (schema : List (String × TelemetryShape)),
      schemaCovers fits table schema = true →
      ∀ entry ∈ table, ∃ shape,
        (entry.1, shape) ∈ schema ∧ fits entry.1 entry.2 shape = true
  | [], _, _, _, member => by cases member
  | (key, item) :: rest, schema, covered, entry, member => by
    simp only [schemaCovers] at covered
    cases located : schemaFrom key schema with
    | nil => simp [located] at covered
    | cons head later =>
      obtain ⟨name, shape⟩ := head
      simp only [located, Bool.and_eq_true] at covered
      obtain ⟨named, members⟩ := schemaFrom_head key schema name shape later located
      subst named
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨shape, members _ (by simp), covered.1⟩
      · obtain ⟨found, inSuffix, fit⟩ :=
          schemaCovers_sound fits rest _ covered.2 entry inRest
        exact ⟨found, members _ inSuffix, fit⟩

inductive BrowserConversion where
  | keep
  | nonFinite
  | unmeasured
  | absentIndex
  | float32
  | float64
  | counts
  | absentIndices

def BrowserConversion.fits (conversion : BrowserConversion) (shape : TelemetryShape) : Bool :=
  match conversion with
  | .keep => true
  | .nonFinite =>
    (match shape with
      | .binary32 | .binary64 => true
      | _ => false)
  | .unmeasured | .absentIndex =>
    (match shape with
      | .optional .natural => true
      | _ => false)
  | .float32 =>
    (match shape with
      | .array _ .binary32 => true
      | _ => false)
  | .float64 =>
    (match shape with
      | .array _ .binary64 => true
      | _ => false)
  | .counts =>
    (match shape with
      | .array _ .natural => true
      | _ => false)
  | .absentIndices =>
    (match shape with
      | .array _ (.optional .natural) => true
      | _ => false)

def TelemetryShape.defaultConversion : TelemetryShape → BrowserConversion
  | .binary32 | .binary64 => .nonFinite
  | .array _ .binary32 => .float32
  | .array _ .binary64 => .float64
  | .array _ .natural => .counts
  | _ => .keep

theorem TelemetryShape.defaultConversion_fits (shape : TelemetryShape) :
    shape.defaultConversion.fits shape = true := by
  cases shape with
  | array count element => cases element <;> rfl
  | _ => rfl

def browserOverrides : List (String × BrowserConversion) :=
  [("core_rss_bytes", .unmeasured), ("checkpoint_bytes", .unmeasured),
   ("checkpoint_write_us", .unmeasured), ("retire_step", .absentIndex),
   ("retire_unit", .absentIndex), ("subtask_unit", .absentIndices)]

def browserConversion (key : String) (shape : TelemetryShape) : BrowserConversion :=
  match browserOverrides.lookup key with
  | some conversion => if conversion.fits shape then conversion else shape.defaultConversion
  | none => shape.defaultConversion

theorem browserConversion_fits (key : String) (shape : TelemetryShape) :
    (browserConversion key shape).fits shape = true := by
  unfold browserConversion
  split
  · split
    · assumption
    · exact shape.defaultConversion_fits
  · exact shape.defaultConversion_fits

theorem browserOverrides_live :
    ∀ entry ∈ browserOverrides, ∃ shape,
      (entry.1, shape) ∈ browserSchema ∧ entry.2.fits shape = true :=
  schemaCovers_sound (fun _ conversion shape => conversion.fits shape)
    browserOverrides browserSchema (by decide +kernel)

def browserIndexBound (key : String) : Option Nat :=
  browserRules.findSome? fun (name, rule) =>
    match rule with
    | .each (.nullable (.range upper)) => if name = key then some upper else none
    | _ => none

def BrowserConversion.indexed (conversion : BrowserConversion) (key : String) : Bool :=
  match conversion with
  | .absentIndices =>
    (match browserIndexBound key with
      | some upper => decide (upper ≤ 2 ^ 31)
      | none => false)
  | _ => true

theorem TelemetryShape.defaultConversion_indexed (shape : TelemetryShape) (key : String) :
    shape.defaultConversion.indexed key = true := by
  cases shape with
  | array count element => cases element <;> rfl
  | _ => rfl

theorem browserOverrides_indexed :
    ∀ entry ∈ browserOverrides, entry.2.indexed entry.1 = true := by
  decide +kernel

theorem browserConversion_indexed (key : String) (shape : TelemetryShape) :
    (browserConversion key shape).indexed key = true := by
  unfold browserConversion
  split
  · next conversion found =>
    obtain ⟨before, after, located, _⟩ := List.lookup_eq_some_iff.mp found
    split
    · exact browserOverrides_indexed (key, conversion) (by rw [located]; simp)
    · exact shape.defaultConversion_indexed key
  · exact shape.defaultConversion_indexed key

def BrowserConversion.number (conversion : BrowserConversion) (shape : TelemetryShape) : Bool :=
  match conversion with
  | .nonFinite | .unmeasured | .absentIndex => conversion.fits shape
  | .keep =>
    (match shape with
      | .natural | .integer | .goalKind | .goalItem => true
      | _ => false)
  | _ => false

def BrowserConversion.numbers (conversion : BrowserConversion) (shape : TelemetryShape) :
    Option Nat :=
  match conversion with
  | .float32 | .float64 | .counts | .absentIndices =>
    if conversion.fits shape then
      (match shape with
        | .array count _ => some count
        | _ => none)
    else none
  | _ => none

def BrowserConversion.javascript : BrowserConversion → String → String
  | .keep, x => x
  | .nonFinite, x | .unmeasured, x => s!"observerNumber({x})"
  | .absentIndex, x => s!"observerIndex({x})"
  | .float32, x => s!"Float32Array.from({x},observerNumber)"
  | .float64, x => s!"Float64Array.from({x},observerNumber)"
  | .counts, x => s!"Float64Array.from({x})"
  | .absentIndices, x => s!"Int32Array.from({x},observerIndex)"

def BrowserConversion.finite : BrowserConversion → Option (String → String)
  | .nonFinite => some fun x => s!"Number.isFinite({x})"
  | .float32 | .float64 => some fun x => s!"{x}.every(Number.isFinite)"
  | _ => none

structure BrowserField where
  key : String
  conversion : BrowserConversion

def browserField (entry : String × TelemetryShape) : BrowserField :=
  ⟨entry.1, browserConversion entry.1 entry.2⟩

def browserRecordFields : List BrowserField := browserSchema.map browserField

theorem browserField_keys (schema : List (String × TelemetryShape)) :
    (schema.map browserField).map BrowserField.key = schema.map Prod.fst := by
  induction schema with
  | nil => rfl
  | cons entry rest step => exact congrArg (List.cons entry.1) step

theorem browserRecord_keys :
    browserRecordFields.map BrowserField.key = browserSchema.map Prod.fst :=
  browserField_keys browserSchema

theorem browserField_fits (entry : String × TelemetryShape) :
    (browserField entry).conversion.fits entry.2 = true :=
  browserConversion_fits entry.1 entry.2

def BrowserField.javascript (field : BrowserField) : String :=
  let key := telemetryString field.key
  let target := "r[" ++ key ++ "]"
  let marked := match field.conversion.finite with
    | some test => "if(!" ++ test target ++ ")n??=" ++ key ++ ";"
    | none => ""
  target ++ "=" ++ field.conversion.javascript ("f[" ++ key ++ "]") ++ ";" ++ marked ++ "\n"

inductive BrowserReading where
  | value
  | twice

structure BrowserProperty where
  name : String
  reading : BrowserReading

def BrowserProperty.fits (key : String) (property : BrowserProperty)
    (shape : TelemetryShape) : Bool :=
  match property.reading with
  | .value => true
  | .twice =>
    (match browserConversion key shape with
      | .float32 => true
      | _ => false)

def BrowserProperty.javascript (key : String) (property : BrowserProperty) : String :=
  let value := "r[" ++ telemetryString key ++ "]"
  let reading := match property.reading with
    | .value => value
    | .twice => s!"Array.from({value},v=>2*v)"
  property.name ++ ":" ++ reading

def browserAgreementView : List (String × BrowserProperty) :=
  [("source_sha256", ⟨"source", .value⟩), ("build_sha256", ⟨"build", .value⟩),
   ("process_started_ms", ⟨"process", .value⟩), ("lifetime_step", ⟨"clock", .value⟩),
   ("agreement_scale", ⟨"scale", .value⟩), ("agreement_started", ⟨"started", .value⟩),
   ("agreement_stopped", ⟨"stopped", .value⟩), ("agreement_score", ⟨"score", .value⟩),
   ("agreement_text", ⟨"text", .value⟩), ("agreement_error", ⟨"error", .value⟩),
   ("agreement_channel_score", ⟨"channelScore", .value⟩),
   ("agreement_channel_text", ⟨"channelText", .value⟩),
   ("agreement_channel_error", ⟨"channelError", .value⟩),
   ("agreement_count", ⟨"count", .value⟩), ("agreement_pending", ⟨"pending", .value⟩),
   ("agreement_censored", ⟨"censored", .value⟩), ("agreement_status", ⟨"status", .value⟩),
   ("agreement_horizon", ⟨"horizon", .value⟩),
   ("agreement_start_first", ⟨"startFirst", .value⟩),
   ("agreement_start_last", ⟨"startLast", .value⟩),
   ("agreement_settlement_first", ⟨"settlementFirst", .value⟩),
   ("agreement_settlement_last", ⟨"settlementLast", .value⟩),
   ("agreement_tail", ⟨"tail", .value⟩), ("agreement_rounding", ⟨"rounding", .value⟩),
   ("agreement_history_clock", ⟨"historyClock", .value⟩),
   ("agreement_history_score", ⟨"historyScore", .value⟩),
   ("settle_stride", ⟨"stride", .value⟩), ("demon_names", ⟨"names", .value⟩),
   ("demon_target_policy", ⟨"policies", .value⟩), ("demon_gamma", ⟨"gamma", .value⟩),
   ("demon_horizon", ⟨"envelope", .twice⟩)]

def browserGoalProgressView : List (String × BrowserProperty) :=
  [("goal_count", ⟨"goals", .value⟩), ("attempt_cap", ⟨"attempts", .value⟩),
   ("step_cap", ⟨"steps", .value⟩), ("goal_progress_invalid", ⟨"invalid", .value⟩),
   ("goal_progress_cycle", ⟨"cycle", .value⟩),
   ("goal_progress_resolved", ⟨"resolved", .value⟩),
   ("goal_progress_attempt", ⟨"attempt", .value⟩),
   ("goal_progress_achieved", ⟨"achieved", .value⟩),
   ("goal_progress_completed_cycle", ⟨"completeCycle", .value⟩),
   ("goal_progress_completed_achieved", ⟨"completeAchieved", .value⟩),
   ("goal_progress_score", ⟨"score", .value⟩), ("curriculum_names", ⟨"names", .value⟩),
   ("curriculum_failed_attempts", ⟨"failed", .value⟩),
   ("curriculum_success_steps", ⟨"successSteps", .value⟩), ("goal", ⟨"activeGoal", .value⟩)]

theorem browserAgreementView_live :
    ∀ entry ∈ browserAgreementView, ∃ shape,
      (entry.1, shape) ∈ browserSchema ∧ BrowserProperty.fits entry.1 entry.2 shape = true :=
  schemaCovers_sound BrowserProperty.fits browserAgreementView browserSchema
    (by decide +kernel)

theorem browserGoalProgressView_live :
    ∀ entry ∈ browserGoalProgressView, ∃ shape,
      (entry.1, shape) ∈ browserSchema ∧ BrowserProperty.fits entry.1 entry.2 shape = true :=
  schemaCovers_sound BrowserProperty.fits browserGoalProgressView browserSchema
    (by decide +kernel)

private def viewJavascript (view : List (String × BrowserProperty)) : String :=
  String.intercalate "," (view.map fun (key, property) => property.javascript key)

def browserRecordJavascript : String :=
  "function observerNumber(v){return v===null?NaN:v;}\n" ++
  "function observerIndex(v){return v===null?-1:v;}\n" ++
  "function observerRecord(f){\nconst r={};let n=null;\n" ++
  String.join (browserRecordFields.map BrowserField.javascript) ++
  "return {rec:r,nonFiniteKey:n,agreement:{" ++ viewJavascript browserAgreementView ++
  ",goalProgress:{" ++ viewJavascript browserGoalProgressView ++ "}}};\n}\n" ++
  "function validate(f){const rejected=observerAdmission(f);if(rejected)return rejected;" ++
  "return observerRecord(f);}\n"

end Acorn.Host.Viewer
