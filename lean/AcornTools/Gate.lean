/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.ModuleInventory
import AcornTools.OwnershipSource

/-! # Ordinary Lean verification

The complete suite in `scripts/verify.sh` invokes this tool after shell and Git
whitespace checks. It uses the provisioned Lean/Lake/native tools.
-/
namespace AcornGate

/-- A failed subprocess stops admission; successful output remains ordinary console output.
With `whole`, the child's output is collected and printed in one piece when it exits, so
checks that run at once do not interleave their lines. -/
def run (cmd : String) (args : Array String := #[]) (cwd : Option System.FilePath := none)
    (env : Array (String × Option String) := #[]) (whole : Bool := false) : IO Unit := do
  let started ← IO.monoMsNow
  let report (status : UInt32) : IO String :=
    return s!"check {cmd}: {(← IO.monoMsNow) - started} ms; status {status}\n"
  let status ← if whole then
      let output ← IO.Process.output { cmd, args, cwd, env, stdin := .null }
      IO.eprint output.stderr
      IO.print (output.stdout ++ (← report output.exitCode))
      pure output.exitCode
    else
      let child ← IO.Process.spawn { cmd, args, cwd, env, stdin := .null }
      let status ← child.wait
      IO.print (← report status)
      pure status
  (← IO.getStdout).flush
  unless status == 0 do throw (IO.userError s!"{cmd} {args} exited {status}")

/-- Run independent checks at once, each on its own thread. Every check is reaped before
any failure is reported, so a refused check cannot leave another running. -/
def together (checks : List (IO Unit)) : IO Unit := do
  let tasks ← checks.mapM fun check => IO.asTask (prio := .dedicated) check
  let mut failures := []
  for task in tasks do
    match task.get with
    | .ok () => pure ()
    | .error error => failures := error.toString :: failures
  unless failures.isEmpty do
    throw (IO.userError (String.intercalate "\n" failures.reverse))

/-- Every build goes through the same local-dependency admission. -/
def lake (args : Array String) : IO Unit :=
  run "lean" (#["-DwarningAsError=true", "-DautoImplicit=false", "--run", "Bootstrap.lean"] ++ args)

/-- The three fixed mutation arms are independent. -/
def audits : IO Unit :=
  together <| [#["audit"], #["audit", "--explore-rate", "annealed"],
      #["audit", "--arm", "differential"]].map fun args =>
    run "lean/.lake/build/bin/acorn-core" args (some "..")

/-- The refusal for a documentation dependency that is not provisioned. -/
def siteUnprovisioned (missing : String) : IO.Error := IO.userError
  s!"missing pinned documentation dependencies ({missing}); see docs/verification.md#platform-setup"

/-- The documentation site in `site/` is a second Lake workspace over this package's
dependency checkouts and pinned Verso. Each locked Git dependency is mapped to its
provisioned checkout, as the bootstrap does for this workspace, so Lake fetches
nothing here. A missing checkout is refused. A package's checkout is the directory Lake
materializes it in, `Name.toString (escape := false)` of its locked name read by
`String.toName` (`PackageEntry.dirName`, Lake of Lean v4.35.0), so the escaped name
`«lean-intent»` has the directory `lean-intent`. -/
def siteOverrides : IO String := do
  let lock ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile "../site/lake-manifest.json"))
  let mut entries : Array Lean.Json := #[]
  for entry in ← IO.ofExcept (lock.getObjValAs? (Array Lean.Json) "packages") do
    unless (← IO.ofExcept (entry.getObjValAs? String "type")) == "git" do continue
    let name ← IO.ofExcept (entry.getObjValAs? String "name")
    let directory := name.toName.toString (escape := false)
    let config ← IO.ofExcept (entry.getObjValAs? String "configFile")
    for component in [directory, config] do
      unless !component.isEmpty && component != "." && component != ".." &&
          component.toList.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.') do
        throw (IO.userError s!"unsupported documentation package component: {component}")
    let dir := s!"../lean/.lake/packages/{directory}"
    unless ← (System.FilePath.mk ".lake/packages" / directory / config).pathExists do
      throw (siteUnprovisioned name)
    entries := entries.push (Lean.Json.mkObj [
      ("name", name), ("scope", ← IO.ofExcept (entry.getObjVal? "scope")),
      ("inherited", ← IO.ofExcept (entry.getObjVal? "inherited")), ("configFile", config),
      ("manifestFile", ← IO.ofExcept (entry.getObjVal? "manifestFile")),
      ("type", "path"), ("dir", dir)])
  IO.FS.createDirAll "../site/.lake"
  IO.FS.writeFile "../site/.lake/acorn-path-packages.json"
    ((Lean.Json.mkObj [("version", "1.2.0"), ("packages", Lean.toJson entries)]).compress ++ "\n")
  return ".lake/acorn-path-packages.json"

/-- Admit and build the documents, which elaborates every reference they make to a Lean owner,
then render them: each kept Markdown file must equal the rendering of its document, or with
`write` is written from it. Verso is a provisioned dependency. Lake itself decides its
readiness: with `--no-build` it exits 3 unless every artifact of `VersoManual` is current,
so verification never compiles a dependency inside its deadline.

No document is elaborated before it is admitted. The site's own tooling (`AcornSite`, under the
owner's paths) is built first. Each document under `site/AcornDocs` is then admitted by
`site/Admit.lean`, which inspects every command of the document before elaborating it, and only
then built: the documents the root includes at once, then the root `AcornDocs`, whose admission
reads their builds. A refusal stops the step before Lake builds the refused document. The
admission and the renderer run interpreted; a linked executable would compile the native code of
every proof module a document imports. `whole` prints each step's output in one piece, for a
check that runs beside others. -/
def site (write : Bool) (whole : Bool := false) : IO Unit := do
  let flags := #["--no-cache", "--wfail", s!"--packages={← siteOverrides}"]
  let env := #[("LAKE_ARTIFACT_CACHE", some "false")]
  let ready ← IO.Process.output {
    cmd := "lake", args := flags ++ #["build", "--no-build", "verso/VersoManual"],
    cwd := some "../site", stdin := .null, env }
  if ready.exitCode == 3 then throw (siteUnprovisioned "Verso is not built")
  unless ready.exitCode == 0 do
    throw (IO.userError s!"Lake could not decide Verso provisioning:\n{ready.stdout}{ready.stderr}")
  let lakeSite (args : Array String) (whole : Bool := whole) : IO Unit :=
    run "lake" (flags ++ args) (some "../site") env whole
  let interpret (program : String) (args : Array String) (whole : Bool := whole) : IO Unit :=
    lakeSite (#["env", "lean", "-DwarningAsError=true", "-DautoImplicit=false", "--run",
      program] ++ args) whole
  let admit (document : Lean.Name) : IO Unit :=
    interpret "Admit.lean" #[document.toString.replace "." "/" ++ ".lean"] (whole := true)
  let root : Lean.Name := `AcornDocs
  let documents := (← AcornModuleInventory.siteModules).filter root.isPrefixOf
  unless documents.contains root do throw (IO.userError "the site has no root document AcornDocs")
  let included := documents.filter (· != root)
  lakeSite #["build", "AcornSite"]
  together (included.toList.map admit)
  unless included.isEmpty do lakeSite (#["build"] ++ included.map ("+" ++ ·.toString))
  admit root
  lakeSite #["build", "AcornSite", "AcornDocs"]
  interpret "Main.lean" (if write then #["write"] else #[])
  IO.println "site: documents admitted, then elaborated against their Lean owners; kept Markdown matches"

/-- Source admission precedes application compilation. Every discovered module is admitted;
the build requests each one that `keep` accepts, with its native object where it has one,
and every declared executable. The two source admissions run at once with Lake's target
inventory, since none depends on another. -/
def admitAndBuild (keep : Lean.Name → Bool) : IO Unit := do
  lake #["build", "lean-boundary-audit"]
  let modules ← AcornOwnershipAudit.sources
  let waiting ← IO.mkRef #[]
  together [
    do waiting.set (← AcornOwnershipAudit.inventory modules).2,
    run ".lake/build/bin/lean-boundary-audit" #["source"] (whole := true),
    run ".lake/build/bin/lean-boundary-audit" #["proof-source"] (whole := true)]
  IO.println "ownership: source modules and Lake entries admitted"
  (← IO.getStdout).flush
  let modules := modules.filter keep
  -- Lake resolves the build graph on one thread, in request order, and that thread waits
  -- for the `needs` of a request before it reads the next one (`Module.recFetchPreSetup`,
  -- Lake of Lean v4.35.0). A request for an executable's root module resolves to that
  -- executable (`Package.findTargetModule?`). So an entry whose `needs` name a target, and
  -- its root module, are requested last: every other job is already scheduled when Lake
  -- starts to wait. The modules lead the rest, so that the proof modules, whose import chain
  -- is the longest in the build, are scheduled first.
  let waiting ← waiting.get
  let late := AcornOwnership.executables.filter fun entry => waiting.contains entry.1
  let (lateModules, modules) := modules.partition fun name => late.any (·.2 == name)
  let (lateTargets, executableTargets) := AcornOwnership.executables.partition late.contains
  let requests (modules : Array Lean.Name) : Array String :=
    modules.map (fun name => "+" ++ name.toString) ++
      (modules.filter AcornModuleInventory.nativeModule).map
        fun name => "+" ++ name.toString ++ ":c.o.export"
  lake (#["build"] ++ requests modules ++ executableTargets.map (·.1) ++
    lateTargets.map (·.1) ++ requests lateModules)

/-- Every discovered module is built, and every declared native entry retains compilation and
execution-route admission. Every admission of the finished build runs at once with the
others, since none depends on another and none writes what another reads. No step here runs
a compiled program of the change: the tools are built from modules under the owner's paths
alone (`AcornBoundaryAudit.toolImports`), and the kept browser kernel is compared with its
emitter's text inside the ownership audit (`AcornBrowserAudit.kernel`). The documents
check runs after them, even when one fails: the documentation workspace requires this package
by path (`site/lakefile.toml`), so its build can write into the build directory that the
admissions read. -/
def verify : IO Unit := do
  admitAndBuild fun _ => true
  let admitted ← (together [
    run ".lake/build/bin/lean-boundary-audit" #["compiled"] (whole := true),
    run ".lake/build/bin/native-audit" (whole := true),
    run ".lake/build/bin/ownership-audit" #["complete"] (whole := true)]).toBaseIO
  site false (whole := true)
  IO.ofExcept admitted
  IO.println "All required Lean checks passed, including proof, execution and corpus admission."

end AcornGate

/-- Failures never trigger provisioning or fall back to another implementation. -/
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [] => AcornGate.verify
    -- The first of the merge gate's two timed stages: the build that the complete command then reuses
    -- where Lake's traces match. The axiom pins import the proof library, so this stage
    -- leaves them out although they are a tool module. It admits nothing after the build.
    | ["build-executing"] =>
      AcornGate.admitAndBuild fun name =>
        !(`AcornVerif).isPrefixOf name && name != `AcornTools.AxiomPins
      IO.println "build-executing: sources admitted; modules outside AcornVerif except axiom pins and entries built"
    | ["diagnostics"] =>
      AcornGate.lake #["build", "acorn-core"]
      AcornGate.audits
      IO.println "Optional mutation diagnostics passed; this is not ordinary merge verification."
    | ["site"] => AcornGate.site false
    | ["site", "write"] => AcornGate.site true
    | _ => throw (IO.userError "usage: acorn-gates [build-executing | diagnostics | site [write]]")
    return 0
  catch error =>
    IO.eprintln s!"acorn-gates: {error}"
    return 1
