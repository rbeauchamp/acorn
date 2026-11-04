/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import LeanIntent.Confirmation.Read
import LeanIntent.Implementation.Read
import AcornVerif.Intent.Awaiting

/-! # `intent-check` executable

The merge gate's run of lean-intent's two checks on Acorn's finished build:
`LeanIntent.Confirmation.Read.check`, which decides whether each deliverable's current revision is
confirmed by answers whose authority traces back to the owner, and
`LeanIntent.Implementation.Read.check`, which decides whether each deliverable names the constant
that implements it, with the proof that it fulfils the record.

* **The modules** are read from Lake, never written here: the libraries among the package's default
  targets, as Lake's evaluated configuration lists them (the Lake script `intentLibraries`), and the
  modules of each, as Lake's `modules` facet lists them (`lake query --json <library>:modules`),
  both through the bootstrap. No library, a library with no module or a module listed twice
  refuses. These are the libraries whose modules Regula's audit claims. The boundary audit lets
  no module it admits reach lean-intent but those of the proof library `AcornVerif`, one of them,
  and of the tool modules, which it does not admit, only this one imports lean-intent, so every
  module that can declare a deliverable, an implementation or an owners' log is among them.
* **One list for both checks.** The program imports those modules into one environment and passes
  the same array to each check, so both read the same modules by construction.
* **The decision.** The gate passes only when the confirmation check finds nothing and the
  implementation check's findings are, as a set, the unimplemented findings of the deliverables
  `awaiting` lists (`AcornVerif.Intent.onlyAwaiting_iff`): another finding of any kind, a listed
  name that is no declared deliverable, and a listed deliverable that the check finds implemented
  each fail it (`AcornVerif.Intent.implemented_of_onlyAwaiting`). Both checks refuse a project with
  no deliverable, so neither passes on finding nothing to check.

It prints what each check read and found, one line each, and exits 0 only on a pass. That the
modules Lake lists are all the package's is trusted with Lake, and what the two checks decide is
lean-intent's, read at the pinned commit (`docs/confirmation.md`, `docs/implementation.md`).
-/

namespace AcornIntentCheck

open Lean

/-- **The deliverables awaiting an implementation**: the one closed list of the gate's code, each
with the issue that tracks its fulfilment proof. The implementation check's unimplemented finding
of a listed deliverable is accepted, and nothing else is; a listed name that is no declared
deliverable, or one that gains an implementation, fails the gate, so the list cannot go stale or
widen silently. Decided on the owner's behalf by the agent supervising Acorn's research, on
2026-11-03: the intent-first method confirms a record before its implementation exists. The list is
retired once lean-intent can declare a deliverable awaiting its implementation itself
(rbeauchamp/lean-intent#52). -/
def awaiting : List (Name × String) :=
  [(`AcornVerif.Intent.Decisions.hashDeliverable, "rbeauchamp/acorn#184")]

/-- The output of the bootstrap run with `args`, from the package directory; an error when it
fails. -/
def bootstrap (args : Array String) : IO String := do
  let output ← IO.Process.output {
    cmd := "lean", args := #["-DwarningAsError=true", "-DautoImplicit=false", "--run",
      "Bootstrap.lean"] ++ args, stdin := .null }
  unless output.exitCode == 0 do
    throw (IO.userError s!"the bootstrap refused {args}: {output.stderr}")
  return output.stdout

/-- The JSON array of strings `text`. -/
def strings (text : String) : IO (Array String) := do
  IO.ofExcept (fromJson? (← IO.ofExcept (Json.parse text)) : Except String (Array String))

/-- The libraries among the package's default targets and their modules, as Lake lists them. -/
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

/-- A confirmation finding, in words. -/
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
  | .unanswered record consequence older refused =>
    s!"{record}: '{consequence}' is not answered at the current revision (older: \
      {older.map (·.toString)}, refused: {refused.map (·.toString)})"
  | .declined record consequence ids =>
    s!"{record}: '{consequence}' is declined by {ids.map (·.toString)}"
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

/-- The heartbeats each check may use, in Lean's unit of a thousand: ten times Lean's default limit
for one declaration, counted from the start of that check. The confirmation check renders each
record and every definition its answers' predicates reach. -/
def heartbeats : Nat := 2000000

/-- `x` run in the environment `env` with its own heartbeat budget, and the heartbeats it used, in
thousands. -/
def inEnvironment {α : Type} (env : Environment) (x : MetaM α) : IO (α × Nat) := do
  let start ← IO.getNumHeartbeats
  let (value, _, _) ← x.toIO
    { fileName := "intent-check", fileMap := default, maxHeartbeats := heartbeats * 1000,
      initHeartbeats := start } { env }
  return (value, ((← IO.getNumHeartbeats) - start) / 1000)

/-- Run both checks on the modules Lake lists and decide the gate. Unsafe only because module
initializers must run for the imported environment's extensions to load, as for every reader of a
compiled environment. -/
unsafe def run : IO Bool := do
  let (libraries, modules) ← projectModules
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (modules.map ({ module := · })) {} (loadExts := true)
  let (deliverables, _) ← inEnvironment env
    (LeanIntent.Confirmation.Read.declaredIn modules ``LeanIntent.Deliverable)
  let (confirmed, confirming) ← inEnvironment env (LeanIntent.Confirmation.Read.check modules)
  let (implemented, implementing) ←
    inEnvironment env (LeanIntent.Implementation.Read.check modules)
  IO.println s!"intent: both checks read the same {modules.size} modules, those Lake lists for \
    the default libraries {libraries.toList}"
  IO.println s!"intent: deliverables declared: {deliverables.toList}"
  IO.println s!"intent: confirmation check: {confirmed.counted.length} answers count, \
    {confirmed.findings.length} findings, {confirming} of {heartbeats} thousand heartbeats"
  IO.println s!"intent: implementation check: {implemented.findings.length} findings, \
    {implementing} of {heartbeats} thousand heartbeats"
  for finding in confirmed.findings do
    IO.println s!"intent: confirmation finding: {describe finding}"
  for (deliverable, value, constant) in implemented.implementations do
    IO.println s!"intent: implementation check: {deliverable} is implemented by {value}, which \
      records {constant.name} of {constant.module}"
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
  return confirmed.findings.isEmpty && !deliverables.isEmpty &&
    AcornVerif.Intent.onlyAwaiting pending implemented.findings

end AcornIntentCheck

/-- Run lean-intent's two checks on the finished build. Takes no arguments. -/
unsafe def main (args : List String) : IO UInt32 := do
  unless args.isEmpty do
    IO.eprintln "usage: intent-check"
    return 2
  try
    if ← AcornIntentCheck.run then
      IO.println "intent: both lean-intent checks pass"
      return 0
    IO.println "intent: the lean-intent checks do not pass"
    return 1
  catch error =>
    IO.eprintln s!"intent-check: {error}"
    return 1
