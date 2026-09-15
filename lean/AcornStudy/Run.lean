/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornStudy.Schema
import AcornStudy.Provenance
import AcornStudy.Comparisons

/-! # Run admission

Only the completed loader publishes a run to consumers. Retained byte identity,
complete inventories and analysis support are checked independently of scientific
assessment. Host IO checks assume files remain stable during one invocation.
-/
namespace AcornStudy

/-- An admitted run has passed complete material and lifecycle validation. -/
structure Run where
  private mk ::
  /-- Semantic identity. -/
  id : Slug
  /-- Protocol revision. -/
  protocol : Revision
  /-- Kind-compatible evidence state. -/
  state : RunState
  /-- Original material declarations. -/
  materials : List Material
  /-- Secondary archives never used by primary analysis. -/
  traces : List TraceArchive
  /-- Executable preserved-data reducer, if available. -/
  analysis : Option Analysis
  /-- Published comparison identities. -/
  comparisons : List String
  /-- Positive population where declared. -/
  population : Option {n : Nat // 0 < n ∧ n < 2^64}
  /-- Explicit limitations and support for historical imports. -/
  historical : Option Historical

/-- Canonical result preference follows the admitted analysis binding. -/
def Run.result (r : Run) : Option LocalPath :=
  r.analysis.map (·.result) |>.orElse (fun _ =>
    (r.materials.find? (fun m => m.role == "result")).map (·.path))

private def canonicalEffect (r : Run) : IO Effect := do
  let some result := r.result | throw (IO.userError "canonical result absent")
  let verdict ← match r.state.format with
    | "baseline-report" => do
      let fields ← checked (← document result).fields
      let some (_, v) := fields.find? (fun p => p.1 == "verdict")
        | throw (IO.userError "canonical report lacks verdict")
      checked v.text
    | "lean-reduction" => do
      let some text := String.fromUTF8? (← readBytes result)
        | throw (IO.userError "canonical result is not UTF-8")
      let verdicts := (text.splitOn "\n").filterMap fun line =>
        if line.startsWith "verdict: " then some ((line.drop 9).toString.dropEndWhile (· == '\r')).toString else none
      let [verdict] := verdicts | throw (IO.userError "canonical output needs one verdict")
      pure verdict.toLower
    | _ => throw (IO.userError "descriptive evidence has no performance verdict")
  checked (effect verdict)

private def verifyMaterials (r : Run) (manifest : LocalPath) (integrity : Integrity)
    (archives : ArchiveCache) : IO (List String) := do
  let mut virtual := []
  let mut containers := []
  for archive in r.traces do
    if containers.contains archive.path.val then throw (IO.userError "duplicate trace archive")
    containers := archive.path.val :: containers
    for member in archive.members do
      if virtual.contains member.val then throw (IO.userError "observation in multiple archives")
      virtual := member.val :: virtual
    archive.verify r.materials integrity archives
  let mut entries := []
  for m in r.materials do
    if m.path.val == manifest.val then throw (IO.userError "run manifest cannot hash itself")
    if entries.contains (m.path.val, m.role) then throw (IO.userError "duplicate material path/role")
    entries := (m.path.val, m.role) :: entries
    if m.role == "trace-archive" && !containers.contains m.path.val then
      throw (IO.userError "trace archive material has no validated member inventory")
    if !virtual.contains m.path.val || (← pathExists m.path.val) then integrity.file m.path m.sha256
  return virtual ++ containers

private def validateCompletion (r : Run) (missing : List String) : IO Unit := do
  for role in ["protocol", "runner", "environment", "analysis", "configuration", "build", "raw", "result"] do
    unless r.materials.any (fun m => m.role == role) ||
        (r.historical.isSome && missing.any (·.startsWith (role ++ ":"))) do
      throw (IO.userError s!"missing role {role}: preserve or disclose historical unavailability")
  unless r.materials.any (fun m => m.role == "result") do throw (IO.userError "completed run lacks result")
  match r.state with
  | .performance (.completed assessment) _ =>
    if r.population.isNone || r.comparisons.isEmpty then throw (IO.userError "completed performance lacks population/comparisons")
    unless (r.materials.filter (fun m => m.role == "result")).length == 1 do
      throw (IO.userError "performance run requires one canonical result")
    let some population := r.population | throw (IO.userError "population absent")
    let some result := r.result | throw (IO.userError "result absent")
    validateComparisons result r.state.format population.val r.comparisons
    unless assessment.label == (← canonicalEffect r).label do
      throw (IO.userError "performance outcome disagrees with canonical verdict")
  | .probe _ | .diagnostic _ =>
    unless r.comparisons.isEmpty do throw (IO.userError "descriptive run has performance comparisons")
  | _ => throw (IO.userError "completed performance assessment absent")
  if r.state.format == "lean-reduction" && r.analysis.isNone then throw (IO.userError "completed reduction lacks analysis")

private def validate (r : Run) (manifest dir : LocalPath) (missing : List String)
    (integrity : Integrity) (archives : ArchiveCache) : IO Unit := do
  let secondary ← verifyMaterials r manifest integrity archives
  let inventoried := r.materials.map (·.path.val)
  for path in ← inventory dir do
    unless path.val == manifest.val || inventoried.contains path.val do
      throw (IO.userError s!"{path.val}: absent from run materials")
  if ["draft", "registered"].contains r.state.state.phase &&
      (r.analysis.isSome || !r.comparisons.isEmpty || r.materials.any (fun m => ["raw", "result"].contains m.role)) then
    throw (IO.userError "unexecuted run carries observations/results/analysis")
  if r.state.state.phase == "completed" then validateCompletion r missing
  match r.historical with
  | some h =>
    unless h.analysis == r.analysis.isSome do throw (IO.userError "analysis support disagrees with availability")
    if h.rerun && !missing.isEmpty then throw (IO.userError "rerun support has missing execution material")
  | none => unless missing.isEmpty do throw (IO.userError "only historical imports admit missing material")
  if let some analysis := r.analysis then
    unless r.materials.any (fun m => m.path.val == analysis.result.val && m.role == "result") do
      throw (IO.userError "analysis result must be inventoried result material")
    for arg in analysis.arguments do
      let inputs ← if (← (System.FilePath.mk arg.val).symlinkMetadata).type == .dir then inventory arg
        else do checkPath arg; pure #[arg]
      if inputs.isEmpty then throw (IO.userError "empty analysis input inventory")
      for input in inputs do
        if secondary.contains input.val then throw (IO.userError "secondary traces cannot be analysis inputs")
        unless inventoried.contains input.val do throw (IO.userError s!"{input.val}: analysis input not hash-bound")

/-- Load a run atomically: failed validation cannot yield a partially admitted run. -/
def loadRun (value : Acorn.Json.Value) (base kind : String) (integrity : Integrity)
    (archives : ArchiveCache) : IO Run := do
  let (id, revisionId, manifest) ← checked (Acorn.Json.decode value do
    return (← slug (← Acorn.Json.text "id"), ← revision (← Acorn.Json.text "protocol"), ← pathField "manifest"))
  let dir ← checked (localPath s!"{base}/runs/{id.val}")
  unless manifest.val == s!"{dir.val}/manifest.json" do throw (IO.userError "wrong run manifest path")
  let (run, missing) ← decodeDocument manifest do
    Acorn.Json.version 2
    unless (← Acorn.Json.text "id") == id.val && (← Acorn.Json.text "protocol") == revisionId.label do
      throw "run reference disagrees with manifest identity"
    let phase ← Acorn.Json.text "lifecycle"
    let outcome ← Acorn.Json.text "outcome"
    let state ← AcornStudy.state kind phase outcome
    let _ ← Acorn.Json.text "reason"
    let state ← runState state (← Acorn.Json.text "format")
    let materials ← (← (← Acorn.Json.take "materials").list).mapM (fun v => do material v)
    let traces ← (← (← Acorn.Json.take "trace_archives").list).mapM (fun v => do traceArchive dir v)
    let retentionValue ← Acorn.Json.text "step_traces"
    retention retentionValue
    if retentionValue == "secondary-archive" then
      if phase == "completed" && traces.isEmpty then throw "completed secondary archive run lacks archives"
    else unless traces.isEmpty do throw "secondary archives disagree with retention decision"
    for m in materials do
      if beneath m.path.val "studies" && !beneath m.path.val base then throw "material belongs to another study"
    let missing ← unique (← Acorn.Json.texts "missing")
    let analysis ← optional AcornStudy.analysis (← Acorn.Json.take "analysis")
    let comparisons ← unique (← Acorn.Json.texts "comparisons")
    for key in comparisons do
      unless key.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'z') || c == '_') do throw "invalid comparison key"
    let population ← optional (fun v => do
      let n ← v.natural
      if h : 0 < n ∧ n < 2^64 then return ⟨n, h⟩ else throw "population must be positive") (← Acorn.Json.take "population")
    let historical ← optional AcornStudy.historical (← Acorn.Json.take "historical")
    return (Run.mk id revisionId state materials traces analysis comparisons population historical, missing)
  validate run manifest dir missing integrity archives
  return run

end AcornStudy
