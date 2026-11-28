import LeanIntent.Confirmation.Read
import LeanIntent.Implementation.Read
import LeanIntent.Required.Read
import LeanIntent.Execution.Read
import AcornVerif.Intent.Awaiting
import AcornTools.TrackedFiles

namespace AcornIntentCheck

open Lean

def awaiting : List (Name × String) :=
  [(`AcornVerif.Intent.Decisions.hashDeliverable, "rbeauchamp/acorn#184"),
    (`AcornVerif.Intent.Decisions.worldInterfaceDeliverable, "rbeauchamp/acorn#213"),
    (`AcornVerif.Intent.Decisions.oneStreamDeliverable, "rbeauchamp/acorn#215")]

def bootstrap (args : Array String) : IO String := do
  let output ← IO.Process.output (← AcornTrackedFiles.bootstrapProcess args)
  unless output.exitCode == 0 do
    throw (IO.userError s!"the bootstrap refused {args}: {output.stderr}")
  return output.stdout

def strings (text : String) : IO (Array String) := do
  IO.ofExcept (fromJson? (← IO.ofExcept (Json.parse text)) : Except String (Array String))

def projectModules : IO (Array String × Array Name) := do
  let libraries ← strings (← bootstrap #["script", "run", "intentLibraries"])
  if libraries.isEmpty then throw (IO.userError "Lake lists no default library")
  let output ← bootstrap (#["query", "--json"] ++ libraries.map (· ++ ":modules"))
  let lines := (output.splitOn "\n").filter (!·.isEmpty)
  unless lines.length == libraries.size do
    throw (IO.userError s!"Lake answered {lines.length} module lists for {libraries.size} libraries")
  let mut modules : Array Name := #[]
  for (library, line) in libraries.toList.zip lines do
    let names ← strings line
    if names.isEmpty then throw (IO.userError s!"Lake lists no module of {library}")
    modules := modules ++ names.map String.toName
  unless modules.toList.eraseDups.length == modules.size do
    throw (IO.userError "Lake lists a module twice")
  return (libraries, modules)

def projectExecutables : IO (Array (Name × Name)) := do
  let output ← bootstrap #["script", "run", "acornTargets"]
  let values ← IO.ofExcept ((← IO.ofExcept (Json.parse output)).getArr?)
  let mut executables : Array (Name × Name) := #[]
  for value in values do
    let target ← IO.ofExcept (value.getObjValAs? String "target")
    let root ← IO.ofExcept (value.getObjValAs? String "module")
    executables := executables.push (Name.mkSimple target, root.toName)
  if executables.isEmpty then throw (IO.userError "Lake lists no executable")
  unless executables.toList.eraseDups.length == executables.size do
    throw (IO.userError "Lake lists an executable twice")
  return executables

def describeQuestion : LeanIntent.Confirmation.Asked → String
  | .restatement => LeanIntent.Confirmation.restatementConsequence
  | .consequence name => s!"consequence '{name}'"

def describe : LeanIntent.Confirmation.Finding → String
  | .noLog => "the project has no owners' log"
  | .severalLogs names => s!"several owners' logs: {names}"
  | .unreadable index => s!"statement {index} of the log is not a printed statement"
  | .noOwners => "the log declares no owner"
  | .severalOwners ids => s!"several owners declarations: {ids.map (·.toString)}"
  | .foreign id => s!"statement {id.toString} belongs to another project"
  | .repeated id => s!"the id {id.toString} is repeated"
  | .noDeliverable => "the project declares no deliverable"
  | .sourceless id => s!"answer {id.toString} records no source"
  | .unanswered record question older refused =>
    s!"{record}: {describeQuestion question} is not answered at the current revision (older: \
      {older.map (·.toString)}, refused: {refused.map (·.toString)})"
  | .declined record question ids =>
    s!"{record}: {describeQuestion question} is declined by {ids.map (·.toString)}"
  | .ownerUnrecorded record ids =>
    s!"{record}: the owner's confirmations {ids.map (·.toString)} are not recorded"
  | .statusDisagrees record consequence ids =>
    s!"{record}: the status of '{consequence}' disagrees with {ids.map (·.toString)}"
  | .fork record consequence => s!"{record}: '{consequence}' is a fork for the owner"
  | .unbacked record consequence stale =>
    s!"{record}: no answer backs the kept answer to '{consequence}' (stale: \
      {stale.map (·.toString)})"
  | .unkept record id => s!"{record}: answer {id.toString} counts and is not kept"
  | .keptDisagrees record consequence =>
    s!"{record}: the status of '{consequence}' disagrees with the answers kept"
  | .undeclared name => s!"{name} says who settled something and no deliverable holds it"

def describeExecution : LeanIntent.Execution.Finding → String
  | .noDeliverable => "the project declares no deliverable"
  | .untied claim => s!"Runs claim {claim} names no declared deliverable"
  | .unknownExecutable claim executable =>
    s!"Runs claim {claim} names unknown executable {executable}"
  | .noEntryPoint executable root =>
    s!"executable {executable} (root {root}) has no compiled main entry point"
  | .unimplemented deliverable executable =>
    s!"executable {executable} claims to run unimplemented deliverable {deliverable}"
  | .unreached deliverable executable impl =>
    s!"executable {executable} does not reach {impl.name} of {impl.module} for {deliverable}"
  | .idleExecutable executable => s!"executable {executable} claims no deliverable"
  | .deliverableNotRun deliverable => s!"deliverable {deliverable} is run by no executable"
  | .noncomputableSubject deliverable executable impl =>
    s!"executable {executable} claims noncomputable subject {impl.name} of {impl.module} for {deliverable}"

def heartbeats : Nat := 2000000

def inEnvironment {α : Type} (env : Environment) (x : MetaM α) : IO (α × Nat) := do
  let start ← IO.getNumHeartbeats
  let (value, _, _) ← x.toIO
    { fileName := "intent-check", fileMap := default, maxHeartbeats := heartbeats * 1000,
      initHeartbeats := start } { env }
  return (value, ((← IO.getNumHeartbeats) - start) / 1000)

def nameParts : Name → List (Sum String Nat)
  | .anonymous => []
  | .str parent part => nameParts parent ++ [.inl part]
  | .num parent part => nameParts parent ++ [.inr part]

def nameToJson (name : Name) : Json :=
  Json.arr <| (nameParts name).toArray.map fun
    | .inl part => Json.str part
    | .inr part => Json.num part

def nameFromJson (json : Json) : Except String Name := do
  let items ← json.getArr?
  items.foldlM (init := Name.anonymous) fun acc item =>
    match item with
    | .str part => return .str acc part
    | .num _ => return .num acc (← item.getNat?)
    | _ => throw s!"invalid encoded Name component: {item.compress}"

def optionNameToJson : Option Name → Json
  | none => Json.null
  | some name => nameToJson name

def optionNameFromJson : Json → Except String (Option Name)
  | .null => return none
  | other => return some (← nameFromJson other)

def constantToJson (constant : LeanIntent.Implementation.Constant) : Json :=
  Json.mkObj [("module", nameToJson constant.module), ("name", nameToJson constant.name)]

def constantFromJson (json : Json) : Except String LeanIntent.Implementation.Constant := do
  let mod ← nameFromJson (← json.getObjVal? "module")
  let name ← nameFromJson (← json.getObjVal? "name")
  return ⟨mod, name⟩

def claimToJson (claim : LeanIntent.Execution.Claim) : Json :=
  Json.mkObj [
    ("name", nameToJson claim.name),
    ("deliverable", optionNameToJson claim.deliverable),
    ("executable", nameToJson claim.executable)]

def claimFromJson (json : Json) : Except String LeanIntent.Execution.Claim := do
  let name ← nameFromJson (← json.getObjVal? "name")
  let deliverable ← optionNameFromJson (← json.getObjVal? "deliverable")
  let executable ← nameFromJson (← json.getObjVal? "executable")
  return ⟨name, deliverable, executable⟩

def executableToJson (executable : LeanIntent.Execution.Executable) : Json :=
  Json.mkObj [
    ("name", nameToJson executable.name),
    ("root", nameToJson executable.root),
    ("entry", toJson executable.entry),
    ("reaches", Json.arr (executable.reaches.toArray.map constantToJson))]

def executableFromJson (json : Json) : Except String LeanIntent.Execution.Executable := do
  let name ← nameFromJson (← json.getObjVal? "name")
  let root ← nameFromJson (← json.getObjVal? "root")
  let entry ← json.getObjValAs? Bool "entry"
  let reaches ← (← (← json.getObjVal? "reaches").getArr?).mapM constantFromJson
  return ⟨name, root, entry, reaches.toList⟩

structure ModulesResult where
  ok : Bool
  summaryLines : Array String
  detailLines : Array String
  deliverables : Array Name
  implementations : Array (Name × LeanIntent.Implementation.Constant)
  awaiting : Array Name
  claims : Array LeanIntent.Execution.Claim
  claimingHeartbeats : Nat

def modulesResultToJson (result : ModulesResult) : Json :=
  Json.mkObj [
    ("ok", toJson result.ok),
    ("summaryLines", toJson result.summaryLines),
    ("detailLines", toJson result.detailLines),
    ("deliverables", Json.arr (result.deliverables.map nameToJson)),
    ("implementations", Json.arr (result.implementations.map fun (d, c) =>
      Json.mkObj [("deliverable", nameToJson d), ("constant", constantToJson c)])),
    ("awaiting", Json.arr (result.awaiting.map nameToJson)),
    ("claims", Json.arr (result.claims.map claimToJson)),
    ("claimingHeartbeats", toJson result.claimingHeartbeats)]

def modulesResultFromJson (json : Json) : Except String ModulesResult := do
  let ok ← json.getObjValAs? Bool "ok"
  let summaryLines ← json.getObjValAs? (Array String) "summaryLines"
  let detailLines ← json.getObjValAs? (Array String) "detailLines"
  let deliverables ← (← (← json.getObjVal? "deliverables").getArr?).mapM nameFromJson
  let implementations ← (← (← json.getObjVal? "implementations").getArr?).mapM fun item => do
    let deliverable ← nameFromJson (← item.getObjVal? "deliverable")
    let constant ← constantFromJson (← item.getObjVal? "constant")
    return (deliverable, constant)
  let awaiting ← (← (← json.getObjVal? "awaiting").getArr?).mapM nameFromJson
  let claims ← (← (← json.getObjVal? "claims").getArr?).mapM claimFromJson
  let claimingHeartbeats ← json.getObjValAs? Nat "claimingHeartbeats"
  return {
    ok, summaryLines, detailLines, deliverables, implementations, awaiting, claims,
    claimingHeartbeats }

def writeStdin
    (child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped })
    (text : String) :
    IO (IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }) := do
  let (stdin, child) ← child.takeStdin
  stdin.putStr text
  stdin.flush
  return child

def runWorker (flag : String) (payload : Json) : IO Json := do
  let app ← IO.appPath
  let child ← IO.Process.spawn {
    cmd := app.toString
    args := #[flag]
    stdin := .piped
    stdout := .piped
    stderr := .piped
  }
  let child ← writeStdin child payload.compress
  let stdoutTask ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← child.stderr.readToEnd
  let exitCode ← child.wait
  let stdout ← IO.ofExcept stdoutTask.get
  unless exitCode == 0 do
    let detail := stderr.trimAscii.toString
    let message := if detail.isEmpty then stdout.trimAscii.toString else detail
    throw (IO.userError message)
  IO.ofExcept (Json.parse stdout)

unsafe def runModulesWorker : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let payload ← IO.ofExcept (Json.parse input)
  let libraries ← IO.ofExcept (payload.getObjValAs? (Array String) "libraries")
  let modules ← IO.ofExcept do
    (← (← payload.getObjVal? "modules").getArr?).mapM nameFromJson
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := true)
  let (deliverables, _) ← inEnvironment env
    (LeanIntent.Confirmation.Read.declaredIn modules ``LeanIntent.Deliverable)
  let (confirmed, confirming) ← inEnvironment env (LeanIntent.Confirmation.Read.check modules)
  let (implemented, implementing) ←
    inEnvironment env (LeanIntent.Implementation.Read.check modules)
  let (required, requiring) ← inEnvironment env (LeanIntent.Required.Read.check modules)
  let (claims, claiming) ← inEnvironment env (LeanIntent.Execution.Read.claims modules)
  let summaryLines : Array String := #[
    s!"intent: all four checks read the same {modules.size} modules, those Lake lists for \
      the default libraries {libraries.toList}",
    s!"intent: deliverables declared: {deliverables.toList}",
    s!"intent: confirmation check: {confirmed.counted.length} answers count, \
      {confirmed.findings.length} findings, {confirming} of {heartbeats} thousand heartbeats",
    s!"intent: implementation check: {implemented.findings.length} findings, \
      {implementing} of {heartbeats} thousand heartbeats",
    s!"intent: required check: {required.theorems.length} theorems, \
      {required.findings.length} findings, {requiring} of {heartbeats} thousand heartbeats"]
  let mut detailLines : Array String := #[]
  for finding in confirmed.findings do
    detailLines := detailLines.push s!"intent: confirmation finding: {describe finding}"
  for (deliverable, value, constant) in implemented.implementations do
    detailLines := detailLines.push
      s!"intent: implementation check: {deliverable} is implemented by {value}, which \
        records {constant.name} of {constant.module}"
  for (deliverable, value, reason) in implemented.awaiting do
    detailLines := detailLines.push
      s!"intent: implementation finding: {deliverable} declares {value} awaiting \
        ({reason}), which Acorn's closed awaiting list refuses"
  let pending := awaiting.map (·.1)
  for finding in implemented.findings do
    match finding with
    | .unimplemented d =>
      match awaiting.find? (·.1 == d) with
      | some (_, issue) =>
        detailLines := detailLines.push
          s!"intent: implementation check: {d} awaits an implementation ({issue})"
      | none =>
        detailLines := detailLines.push s!"intent: implementation finding: {d} is not implemented"
    | other =>
      detailLines := detailLines.push s!"intent: implementation finding: {repr other}"
  for d in pending do
    unless implemented.findings.contains (.unimplemented d) do
      detailLines := detailLines.push
        s!"intent: {d} is listed as awaiting an implementation, and the check finds no \
          unimplemented deliverable of that name"
  for (value, reason) in required.deferredO2Run do
    detailLines := detailLines.push s!"intent: required check: {value} defers O2Run ({reason})"
  for (value, direction, reason) in required.unprovedComparisons do
    detailLines := detailLines.push
      s!"intent: required check: {value} leaves {direction} comparison unproved ({reason})"
  for (value, reason) in required.casesComparisons do
    detailLines := detailLines.push
      s!"intent: required check: {value} compares by concrete cases ({reason})"
  for finding in required.findings do
    detailLines := detailLines.push s!"intent: required finding: {finding.message}"
  if required.theorems.isEmpty then
    detailLines := detailLines.push "intent: required finding: no Required theorems were checked"
  let ok := confirmed.findings.isEmpty && !deliverables.isEmpty &&
    implemented.awaiting.isEmpty &&
    AcornVerif.Intent.onlyAwaiting pending implemented.findings &&
    required.findings.isEmpty && !required.theorems.isEmpty
  let result : ModulesResult := {
    ok
    summaryLines
    detailLines
    deliverables
    implementations := (implemented.implementations.map fun (d, _, c) => (d, c)).toArray
    awaiting := (implemented.awaiting.map (·.1)).toArray
    claims
    claimingHeartbeats := claiming
  }
  IO.println (modulesResultToJson result).compress

def runExecutableWorker : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  let payload ← IO.ofExcept (Json.parse input)
  let name ← IO.ofExcept (nameFromJson (← IO.ofExcept (payload.getObjVal? "name")))
  let root ← IO.ofExcept (nameFromJson (← IO.ofExcept (payload.getObjVal? "root")))
  let targets ← IO.ofExcept do
    (← (← payload.getObjVal? "targets").getArr?).mapM constantFromJson
  initSearchPath (← findSysroot)
  let start ← IO.getNumHeartbeats
  let stored ← LeanIntent.Imported.stored root {}
  let exe ← match LeanIntent.Execution.Read.executableIn stored name root targets.toList with
    | .ok exe => pure exe
    | .error why => throw (IO.userError why)
  let used := ((← IO.getNumHeartbeats) - start) / 1000
  IO.println (Json.mkObj [
    ("executable", executableToJson exe),
    ("heartbeats", toJson used)]).compress

def run : IO Bool := do
  AcornTrackedFiles.verifyGitRoot ".." "" true
  let (libraries, modules) ← projectModules
  let executables ← projectExecutables
  let phase1Json ← runWorker "--worker-modules" <| Json.mkObj [
    ("libraries", toJson libraries),
    ("modules", Json.arr (modules.map nameToJson))]
  let phase1 ← IO.ofExcept (modulesResultFromJson phase1Json)
  let mut checkedExecutables : Array LeanIntent.Execution.Executable := #[]
  let mut executing := phase1.claimingHeartbeats
  let is := phase1.implementations.toList
  let cls := phase1.claims.toList
  for (name, root) in executables do
    let targets := (cls.filter (·.executable == name)).flatMap fun cl =>
      is.filterMap fun (d, c) => if cl.deliverable == some d then some c else none
    let response ← try
      runWorker "--worker-executable" <| Json.mkObj [
        ("name", nameToJson name),
        ("root", nameToJson root),
        ("targets", Json.arr (targets.eraseDups.toArray.map constantToJson))]
    catch err =>
      throw (IO.userError
        s!"the executable {name}, whose root module is {root}, cannot be read: {err}")
    let exe ← IO.ofExcept (executableFromJson (← IO.ofExcept (response.getObjVal? "executable")))
    unless exe.name == name && exe.root == root do
      throw (IO.userError
        s!"executable worker returned {exe.name} ({exe.root}) for {name} ({root})")
    let used ← IO.ofExcept (response.getObjValAs? Nat "heartbeats")
    checkedExecutables := checkedExecutables.push exe
    executing := executing + used
  let executed := LeanIntent.Execution.report phase1.deliverables.toList is
    phase1.awaiting.toList checkedExecutables.toList cls
  for line in phase1.summaryLines do
    IO.println line
  IO.println s!"intent: execution check (strict := false): {executables.size} executables, \
    {executed.reached.length} reached, {executed.awaiting.length} awaiting, \
    {executed.notRun.length} not run, {executed.idle.length} idle, \
    {executed.findings.length} findings, {executing} of {heartbeats} thousand heartbeats"
  for line in phase1.detailLines do
    IO.println line
  for (deliverable, executable, constant) in executed.reached do
    IO.println s!"intent: execution check: {executable} reaches {constant.name} of \
      {constant.module} for {deliverable}"
  for (deliverable, executable) in executed.awaiting do
    IO.println s!"intent: execution check: {executable} awaits implementation of {deliverable}"
  for deliverable in executed.notRun do
    IO.println s!"intent: execution check: {deliverable} is run by no executable"
  for executable in executed.idle do
    IO.println s!"intent: execution check: {executable} claims no deliverable"
  for finding in executed.findings do
    IO.println s!"intent: execution finding: {describeExecution finding}"
  return phase1.ok && executed.findings.isEmpty

end AcornIntentCheck

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    try
      if ← AcornIntentCheck.run then
        IO.println "intent: all four lean-intent checks pass"
        return 0
      IO.println "intent: the lean-intent checks do not pass"
      return 1
    catch error =>
      IO.eprintln s!"intent-check: {error}"
      return 1
  | ["--worker-modules"] =>
    try
      AcornIntentCheck.runModulesWorker
      return 0
    catch error =>
      IO.eprintln s!"{error}"
      return 1
  | ["--worker-executable"] =>
    try
      AcornIntentCheck.runExecutableWorker
      return 0
    catch error =>
      IO.eprintln s!"{error}"
      return 1
  | _ =>
    IO.eprintln "usage: intent-check"
    return 2
