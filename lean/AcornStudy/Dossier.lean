/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornStudy.Run
import AcornStudy.Registration

/-! # Complete study registry

Dossier discovery owns protocol/run identity, integrity and all consumer lookup.
A failure returns no registry. Ordinary discovery authenticates no timestamps;
the optional stronger timing claim has a separate command.
-/
namespace AcornStudy

/-- A study published only after complete inventory and state admission. -/
structure Study where
  private mk ::
  /-- Semantic identity. -/
  slug : Slug
  /-- Scientific question. -/
  question : String
  /-- Kind-specific scientific state. -/
  state : State
  /-- Distinct declared Alberta Plan steps. -/
  planSteps : List Nat
  /-- Protocols with decreasing ancestry. -/
  protocols : List Protocol
  /-- Admitted observed runs. -/
  runs : List Run
  /-- Preserved source associations. -/
  provenance : Provenance
  /-- Structurally inspected optional timestamp evidence. -/
  timestamps : List TimestampEvidence

private def exactDirectories (path : String) (expected : List String) : IO Unit := do
  let root ← checked (localPath path)
  let actual ← if !(← pathExists path) && expected.isEmpty then pure #[] else directories root
  unless actual.toList == expected.mergeSort (· ≤ ·) do
    throw (IO.userError s!"{path}: directory inventory differs from metadata")

private def validateStudy (s : Study) (base : String) (integrity : Integrity) : IO (List TimestampEvidence) := do
  checkPath (← checked (localPath s!"{base}/README.md"))
  let protocols ← checked (unique (s.protocols.map (·.id.label)))
  let runs ← checked (unique (s.runs.map (·.id.val)))
  exactDirectories s!"{base}/protocols" protocols
  exactDirectories s!"{base}/runs" runs
  if s.protocols.isEmpty && s.state.phase != "draft" then throw (IO.userError "non-draft study lacks protocol")
  let mut timestamps := []
  for p in s.protocols do
    checkPath p.document
    if let some original := p.original then checkPath original
    if let some parent := p.parent then
      unless protocols.contains parent.label do throw (IO.userError "unknown parent protocol")
    if let some path := p.registration then
      if let some timestamp ← inspectRegistration path (p.original.getD p.document) base s.provenance.history integrity then
        timestamps := timestamps ++ [timestamp]
  for r in s.runs do
    let some p := s.protocols.find? (fun p => p.id.val == r.protocol.val)
      | throw (IO.userError "unknown run protocol")
    unless r.state.state.phase == "draft" || r.materials.any (fun m =>
        m.path.val == p.document.val || p.original.any (fun o => o.val == m.path.val)) do
      throw (IO.userError "run lacks material binding its protocol")
    for m in r.materials do
      let associated : Bool := match m.role with
        | "registration" => s.protocols.any (fun p => p.registration.any (fun x => x.val == m.path.val))
        | "timestamp-response" => timestamps.any (fun t => t.reply.val == m.path.val)
        | _ => true
      unless associated do throw (IO.userError "retained registration material lacks protocol association")
  let statuses := s.runs.map (·.state.state.phase)
  let legal := match s.state.phase with
    | "draft" => statuses.all (· == "draft")
    | "registered" => !s.protocols.isEmpty && statuses.all (· == "registered")
    | "running" => statuses.contains "running"
    | "completed" => statuses.contains "completed" && statuses.all (fun x => ["completed", "aborted"].contains x)
    | "aborted" => !statuses.isEmpty && statuses.all (· == "aborted")
    | _ => false
  unless legal do throw (IO.userError "study lifecycle disagrees with run inventory")
  if let .performance (.completed assessment) := s.state then
    let effects := s.runs.filterMap fun r => match r.state with
      | .performance (.completed e) _ => some e.label
      | _ => none
    let first :: rest := effects | throw (IO.userError "completed study lacks assessed result")
    let derived := if rest.all (· == first) then first else "inconclusive"
    unless assessment.label == derived do throw (IO.userError "study outcome disagrees with canonical run assessments")
  return timestamps

private def loadStudy (path : LocalPath) (integrity : Integrity) (archives : ArchiveCache) : IO Study := do
  let (id, question, state, steps, protocols, runValues, provenancePath) ← decodeDocument path do
    Acorn.Json.version 2
    let id ← slug (← Acorn.Json.text "slug")
    unless path.val == s!"studies/{id.val}/study.json" do throw "study slug disagrees with directory"
    let provenancePath ← optionalPath "provenance"
    let question ← Acorn.Json.text "question"
    retentionDeclaration (← Acorn.Json.take "retention")
    let kind ← Acorn.Json.text "kind"
    let state ← AcornStudy.state kind (← Acorn.Json.text "lifecycle") (← Acorn.Json.text "outcome")
    let steps ← (← (← Acorn.Json.take "plan_steps").list).mapM (fun v => do v.natural)
    let steps ← unique steps
    unless steps.all (fun n => 1 ≤ n && n ≤ 12) do throw "plan steps outside 1..12"
    for key in ["mechanisms", "departures", "frontier"] do
      let _ ← unique (← Acorn.Json.texts key)
    let protocols ← (← (← Acorn.Json.take "protocols").list).mapM (fun v => do protocol s!"studies/{id.val}" v)
    return (id, question, state, steps.mergeSort (· ≤ ·), protocols, ← (← Acorn.Json.take "runs").list, provenancePath)
  let base := s!"studies/{id.val}"
  let provenance ← loadProvenance provenancePath base integrity archives
  let runs ← runValues.mapM (fun v => loadRun v base state.kind integrity archives)
  let study := Study.mk id question state steps protocols runs provenance []
  let timestamps ← validateStudy study base integrity
  provenance.validateInventory base integrity
  return { study with timestamps := timestamps }

/-- Complete registry; failed discovery never exposes a partial list. -/
structure Registry where
  private mk ::
  /-- All admitted dossiers in semantic identity order. -/
  studies : List Study
  /-- Hash-inventoried source provenance paths. -/
  archived : List String

/-- Discover every dossier from disk with one ephemeral identity cache. -/
def discover : IO Registry := do
  if ← pathExists "evidence" then throw (IO.userError "central evidence directory is not a research owner")
  let root ← checked (localPath "studies")
  checkPath root true
  let mut identities := []
  for entry in ← (System.FilePath.mk "studies").readDir do
    unless ["README.md", ".DS_Store"].contains entry.fileName do
      unless (← entry.path.symlinkMetadata).type == .dir do throw (IO.userError "non-dossier in studies/")
      identities := (← checked (slug entry.fileName)).val :: identities
  if identities.isEmpty then throw (IO.userError "no study dossiers discovered")
  let integrity ← Integrity.create
  let archives ← ArchiveCache.create
  let studies ← (identities.mergeSort (· ≤ ·)).mapM fun id => do
    loadStudy (← checked (localPath s!"studies/{id}/study.json")) integrity archives
  let archived := (← integrity.paths).toList.filter (fun p => p.startsWith "studies/" && (p.splitOn "/").contains "provenance")
  return ⟨studies, archived⟩

/-- Resolve an exact study/protocol/run/comparison citation. -/
def Registry.resolves (r : Registry) (citation : String) : Bool :=
  if !citation.startsWith "study:" then false else
  match (citation.drop 6).toString.splitOn "/" with
  | [id, protocol, run, key] => r.studies.any fun s => s.slug.val == id && s.runs.any fun x =>
      x.protocol.label == protocol && x.id.val == run && x.comparisons.contains key
  | _ => false

/-- Source citations resolve only through admitted preserved catalog membership. -/
def Registry.archive (r : Registry) (revision path : String) : Bool :=
  r.studies.any fun s => s.provenance.sources.any (fun p => p.1 == revision && p.2.contains path)

/-- Archival disposition follows individually inventoried evidence, never neighbors. -/
def Registry.archivalFile (r : Registry) (path : String) : Bool :=
  r.archived.contains path || r.studies.any fun s =>
    s.protocols.any (fun p => p.original.any (fun x => x.val == path)) || s.runs.any fun run =>
      run.materials.any fun m => m.path.val == path &&
        (path.startsWith s!"studies/{s.slug.val}/runs/" ||
          (path.endsWith ".tar.gz" && path.startsWith s!"studies/{s.slug.val}/registration/{run.protocol.label}/" &&
            s.protocols.any (fun p => p.id.val == run.protocol.val && p.registration.isSome)))

/-- The index is derived from all dossiers, with no manually maintained study list. -/
def Registry.index (r : Registry) : String :=
  let header := "# Studies\n\nGenerated by `gates -- study-index` from every study dossier. Scientific coverage remains owned by [design.md](../docs/design.md).\n\n| Study | Kind | Lifecycle | Outcome | Alberta Plan steps |\n|---|---|---|---|---|\n"
  r.studies.foldl (fun text s =>
    let steps := String.intercalate ", " (s.planSteps.map toString)
    let question := s.question.replace "|" "\\|" |>.replace "\n" " " |>.replace "\r" " "
    text ++ s!"| [{s.slug.val}]({s.slug.val}/README.md) — {question} | {s.state.kind} | {s.state.phase} | {s.state.outcome} | {steps} |\n") header

end AcornStudy
