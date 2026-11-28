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

unsafe def run : IO Bool := do
  AcornTrackedFiles.verifyGitRoot ".." "" true
  let (libraries, modules) ← projectModules
  let executables ← projectExecutables
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := true)
  let (deliverables, _) ← inEnvironment env
    (LeanIntent.Confirmation.Read.declaredIn modules ``LeanIntent.Deliverable)
  let (confirmed, confirming) ← inEnvironment env (LeanIntent.Confirmation.Read.check modules)
  let (implemented, implementing) ←
    inEnvironment env (LeanIntent.Implementation.Read.check modules)
  let (required, requiring) ← inEnvironment env (LeanIntent.Required.Read.check modules)
  let (executed, executing) ←
    inEnvironment env (LeanIntent.Execution.Read.check modules executables (strict := false))
  IO.println s!"intent: all four checks read the same {modules.size} modules, those Lake lists for \
    the default libraries {libraries.toList}"
  IO.println s!"intent: deliverables declared: {deliverables.toList}"
  IO.println s!"intent: confirmation check: {confirmed.counted.length} answers count, \
    {confirmed.findings.length} findings, {confirming} of {heartbeats} thousand heartbeats"
  IO.println s!"intent: implementation check: {implemented.findings.length} findings, \
    {implementing} of {heartbeats} thousand heartbeats"
  IO.println s!"intent: required check: {required.theorems.length} theorems, \
    {required.findings.length} findings, {requiring} of {heartbeats} thousand heartbeats"
  IO.println s!"intent: execution check (strict := false): {executables.size} executables, \
    {executed.reached.length} reached, {executed.awaiting.length} awaiting, \
    {executed.notRun.length} not run, {executed.idle.length} idle, \
    {executed.findings.length} findings, {executing} of {heartbeats} thousand heartbeats"
  for finding in confirmed.findings do
    IO.println s!"intent: confirmation finding: {describe finding}"
  for (deliverable, value, constant) in implemented.implementations do
    IO.println s!"intent: implementation check: {deliverable} is implemented by {value}, which \
      records {constant.name} of {constant.module}"
  for (deliverable, value, reason) in implemented.awaiting do
    IO.println s!"intent: implementation finding: {deliverable} declares {value} awaiting \
      ({reason}), which Acorn's closed awaiting list refuses"
  let pending := awaiting.map (·.1)
  for finding in implemented.findings do
    match finding with
    | .unimplemented d =>
      match awaiting.find? (·.1 == d) with
      | some (_, issue) =>
        IO.println s!"intent: implementation check: {d} awaits an implementation ({issue})"
      | none => IO.println s!"intent: implementation finding: {d} is not implemented"
    | other => IO.println s!"intent: implementation finding: {repr other}"
  for d in pending do
    unless implemented.findings.contains (.unimplemented d) do
      IO.println s!"intent: {d} is listed as awaiting an implementation, and the check finds no \
        unimplemented deliverable of that name"
  for (value, reason) in required.deferredO2Run do
    IO.println s!"intent: required check: {value} defers O2Run ({reason})"
  for (value, direction, reason) in required.unprovedComparisons do
    IO.println s!"intent: required check: {value} leaves {direction} comparison unproved ({reason})"
  for (value, reason) in required.casesComparisons do
    IO.println s!"intent: required check: {value} compares by concrete cases ({reason})"
  for finding in required.findings do
    IO.println s!"intent: required finding: {finding.message}"
  if required.theorems.isEmpty then
    IO.println "intent: required finding: no Required theorems were checked"
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
  return confirmed.findings.isEmpty && !deliverables.isEmpty &&
    implemented.awaiting.isEmpty &&
    AcornVerif.Intent.onlyAwaiting pending implemented.findings &&
    required.findings.isEmpty && !required.theorems.isEmpty &&
    executed.findings.isEmpty

end AcornIntentCheck

unsafe def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "usage: intent-check"
    return 2
  try
    if ← AcornIntentCheck.run then
      IO.println "intent: all four lean-intent checks pass"
      return 0
    IO.println "intent: the lean-intent checks do not pass"
    return 1
  catch error =>
    IO.eprintln s!"intent-check: {error}"
    return 1
