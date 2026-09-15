/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornStudy.Files

/-! # Dossier schema

Pure admission owns spelling, protocol ancestry and kind-specific evidence formats.
Filesystem correspondence is checked by the dossier loader before consumer access.
-/
namespace AcornStudy

/-- Canonical positive machine-width revision. -/
abbrev Revision := {n : Nat // 0 < n ∧ n < 2^64}

/-- Canonical revision presentation is derived from the stored number. -/
def Revision.label (r : Revision) : String := s!"v{r.val}"

/-- Admit canonical revision spellings without aliases. -/
def revision (s : String) : Except String Revision := do
  let some n := (s.drop 1).toString.toNat? | throw "invalid revision"
  if h : 0 < n ∧ n < 2^64 then
    let r : Revision := ⟨n, h⟩
    if r.label == s then return r else throw "noncanonical revision"
  else throw "revision outside positive u64 domain"

/-- Duplicate declarations are rejected rather than silently deduplicated. -/
def unique {α : Type} [BEq α] (xs : List α) : Except String (List α) := do
  if xs.length == xs.eraseDups.length then return xs else throw "duplicate declaration"

/-- Decode an optional value; only null denotes absence. -/
def optional {α : Type} (f : Acorn.Json.Value → Except String α) (v : Acorn.Json.Value) : Except String (Option α) :=
  match v.optional with
  | none => .ok none
  | some v => some <$> f v

/-- Kind-specific scientific effect admission. -/
def effect : String → Except String Effect
  | "supported" => .ok .supported
  | "refuted" => .ok .refuted
  | "inconclusive" => .ok .inconclusive
  | _ => .error "unknown performance assessment"

/-- Human-readable effect label. -/
def Effect.label : Effect → String
  | .supported => "supported"
  | .refuted => "refuted"
  | .inconclusive => "inconclusive"

/-- A lifecycle label is derived from its constructor. -/
def Lifecycle.label {α : Type} : Lifecycle α → String
  | .draft => "draft"
  | .registered => "registered"
  | .running => "running"
  | .completed _ => "completed"
  | .aborted => "aborted"

/-- Non-completed lifecycles cannot report an assessment. -/
def Lifecycle.outcome {α : Type} (label : α → String) : Lifecycle α → String
  | .completed a => label a
  | _ => "not-assessed"

/-- Study kind derived from the state constructor. -/
def State.kind : State → String
  | .performance _ => "performance-comparison"
  | .probe _ => "observational-probe"
  | .diagnostic _ => "operational-diagnostic"

/-- Phase derived from the state constructor. -/
def State.phase : State → String
  | .performance s => s.label
  | .probe s | .diagnostic s => s.label

/-- Assessment derived from the kind-specific state constructor. -/
def State.outcome : State → String
  | .performance s => s.outcome Effect.label
  | .probe s | .diagnostic s => s.outcome (fun _ => "descriptive")

/-- The two performance evidence representations. -/
inductive PerformanceFormat where
  /-- Native preserved-data reduction. -/
  | lean
  /-- Original baseline report. -/
  | baseline

/-- Evidence format and kind share one constructor, preventing contradictory writes. -/
inductive RunState where
  /-- Performance evidence carries a performance format. -/
  | performance (phase : Lifecycle Effect) (format : PerformanceFormat)
  /-- Probe evidence is command output. -/
  | probe (phase : Lifecycle Unit)
  /-- Diagnostic evidence is a diagnostic report. -/
  | diagnostic (phase : Lifecycle Unit)

/-- Scientific state projection preserves the kind and phase by construction. -/
def RunState.state : RunState → State
  | .performance s _ => .performance s
  | .probe s => .probe s
  | .diagnostic s => .diagnostic s

/-- Run format projection cannot disagree with the kind. -/
def RunState.format : RunState → String
  | .performance _ .lean => "lean-reduction"
  | .performance _ .baseline => "baseline-report"
  | .probe _ => "command-output"
  | .diagnostic _ => "diagnostic"

/-- Attach only a kind-compatible format. -/
def runState (s : State) (format : String) : Except String RunState :=
  match s, format with
  | .performance p, "lean-reduction" => .ok (.performance p .lean)
  | .performance p, "baseline-report" => .ok (.performance p .baseline)
  | .probe p, "command-output" => .ok (.probe p)
  | .diagnostic p, "diagnostic" => .ok (.diagnostic p)
  | _, _ => .error "study kind disagrees with evidence format"

/-- Every admitted format retains exactly the supplied scientific state. -/
theorem runState_preserves (s : State) (f : String) (r : RunState)
    (h : runState s f = .ok r) : r.state = s := by
  unfold runState at h
  split at h <;> cases h <;> rfl

/-- A protocol parent is strictly earlier, so ancestry cannot cycle. -/
structure Protocol where
  /-- Positive canonical revision. -/
  id : Revision
  /-- Initial v1 or a strictly decreasing parent. -/
  parent : Option Revision
  /-- Every admission carries the ancestry relation. -/
  ancestry : match parent with | none => id.val = 1 | some p => p.val < id.val
  /-- Semantic presentation. -/
  document : LocalPath
  /-- Preserved original bytes, distinct from the presentation. -/
  original : Option LocalPath
  /-- Optional retained registration. -/
  registration : Option LocalPath

/-- Pure protocol identity and ancestry admission. -/
def protocol (base : String) (v : Acorn.Json.Value) : Except String Protocol := Acorn.Json.decode v do
  let id ← revision (← Acorn.Json.text "id")
  let parent ← optional (fun v => do revision (← v.text)) (← Acorn.Json.take "parent")
  let document ← localPath (← Acorn.Json.text "document")
  unless document.val == s!"{base}/protocols/{id.label}/protocol.md" do throw "wrong protocol presentation path"
  let original ← optional (fun v => do localPath (← v.text)) (← Acorn.Json.take "original")
  let registration ← optional (fun v => do localPath (← v.text)) (← Acorn.Json.take "registration")
  for path in original.toList ++ registration.toList do
    unless beneath path.val base do throw "protocol evidence belongs to another study"
  if original.any (fun p => p.val == document.val) then throw "original protocol aliases presentation"
  let _ ← Acorn.Json.text "prior_data_access"
  match parent with
  | none =>
    if h : id.val = 1 then return ⟨id, none, h, document, original, registration⟩
    else throw "only v1 is initial"
  | some p =>
    if h : p.val < id.val then return ⟨id, some p, h, document, original, registration⟩
    else throw "every amendment requires an earlier parent"

/-- Available analysis is a shell-free executable and explicit confined input list. -/
structure Analysis where
  /-- Bare executable name. -/
  executable : Slug
  /-- Explicit preserved inputs. -/
  arguments : List LocalPath
  /-- Canonical output bytes. -/
  result : LocalPath

/-- Admit an analysis command with at least one bound input. -/
def analysis (v : Acorn.Json.Value) : Except String Analysis := Acorn.Json.decode v do
  let executable ← slug (← Acorn.Json.text "executable")
  let arguments ← (← Acorn.Json.texts "arguments").mapM (fun s => do localPath s)
  if arguments.isEmpty then throw "analysis must bind input arguments"
  return ⟨executable, arguments, ← localPath (← Acorn.Json.text "result")⟩

/-- Historical availability is a support declaration, never a successful rerun. -/
structure Historical where
  /-- Preserved-data analysis availability. -/
  analysis : Bool
  /-- Original experiment execution availability. -/
  rerun : Bool

/-- Decode explicit availability vocabulary. -/
def support : String → Except String Bool
  | "supported" => .ok true
  | "unavailable" => .ok false
  | _ => .error "unknown support status"

/-- Historical imports must state their limitations. -/
def historical (v : Acorn.Json.Value) : Except String Historical := Acorn.Json.decode v do
  let analysis ← support (← Acorn.Json.text "analysis_reproduction")
  let rerun ← support (← Acorn.Json.text "experiment_rerun")
  if (← Acorn.Json.texts "limitations").isEmpty then throw "historical imports require limitations"
  return ⟨analysis, rerun⟩

/-- Retention vocabulary admission. -/
def retention (s : String) : Except String Unit :=
  if ["not-retained", "secondary-archive", "essential"].contains s then .ok ()
  else .error "unknown step-trace retention decision"

/-- Study-level retention states essential evidence and a scientific rationale. -/
def retentionDeclaration (v : Acorn.Json.Value) : Except String Unit := Acorn.Json.decode v do
  if (← unique (← Acorn.Json.texts "essential")).isEmpty then throw "empty essential evidence"
  retention (← Acorn.Json.text "step_traces")
  let _ ← Acorn.Json.text "rationale"
  let _ ← Acorn.Json.text "reproduction"

end AcornStudy
