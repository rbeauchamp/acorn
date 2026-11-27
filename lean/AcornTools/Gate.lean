import AcornTools.ModuleInventory
import AcornTools.OwnershipSource
import AcornTools.TrackedFiles

namespace AcornGate

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

def together (checks : List (IO Unit)) : IO Unit := do
  let tasks ← checks.mapM fun check => IO.asTask (prio := .dedicated) check
  let mut failures := []
  for task in tasks do
    match task.get with
    | .ok () => pure ()
    | .error error => failures := error.toString :: failures
  unless failures.isEmpty do
    throw (IO.userError (String.intercalate "\n" failures.reverse))

def lake (args : Array String) : IO Unit := do
  let process ← AcornTrackedFiles.bootstrapProcess args
  run process.cmd process.args

def audits : IO Unit :=
  together <| [#["audit"], #["audit", "--explore-rate", "annealed"],
      #["audit", "--arm", "differential"]].map fun args =>
    run "lean/.lake/build/bin/acorn-core" args (some "..")

def siteUnprovisioned (missing : String) : IO.Error := IO.userError
  s!"missing pinned documentation dependencies ({missing}); see docs/verification.md#platform-setup"

def siteOverrides (requireClean : Bool := true) : IO String := do
  let admitArgs := if requireClean then
    #["admit-site", "--clean", "--emit-overrides", ".."]
  else
    #["admit-site", "--emit-overrides", ".."]
  let text ← AcornTrackedFiles.runTrackedHelperStdout ".." admitArgs requireClean
  if text.isEmpty then
    throw (IO.userError "empty documentation dependency overrides")
  let dirArgs := if requireClean then
    #["admit-lake-dirs", "--clean", "--workspace", "site", ".."]
  else
    #["admit-lake-dirs", "--workspace", "site", ".."]
  IO.FS.createDirAll "../site/.lake"
  AcornTrackedFiles.runTrackedHelper ".." dirArgs requireClean
  let overridePath : System.FilePath := "../site/.lake/acorn-path-packages.json"
  let current ← try some <$> IO.FS.readFile overridePath catch _ => pure none
  unless current == some text do
    AcornTrackedFiles.writeFileAtomicExclusive overridePath text
  return ".lake/acorn-path-packages.json"

def site (write : Bool) (whole : Bool := false) : IO Unit := do
  let requireClean := !write
  AcornOwnershipAudit.siteModuleInventory requireClean
  let flags := #["-f", "lakefile.toml", "--no-cache", "--wfail",
    s!"--packages={← siteOverrides requireClean}"]
  let env := #[("LAKE_ARTIFACT_CACHE", some "false")]
  let ready ← IO.Process.output {
    cmd := "lake", args := flags ++ #["build", "--no-build", "verso/VersoManual"],
    cwd := some "../site", stdin := .null, env }
  if ready.exitCode == 3 then throw (siteUnprovisioned "Verso is not built")
  unless ready.exitCode == 0 do
    throw (IO.userError s!"Lake could not decide Verso provisioning:\n{ready.stdout}{ready.stderr}")
  run "lake" (flags ++ #["build", "AcornSite", "AcornDocs"]) (some "../site") env whole
  run "lake" (flags ++ #["env", "lean", "-DwarningAsError=true", "-DautoImplicit=false", "--run",
    "Main.lean"] ++ (if write then #["write"] else #[])) (some "../site") env whole
  IO.println "site: documents elaborated against their Lean owners; kept Markdown matches"

def admitAndBuild (keep : Lean.Name → Bool) : IO Unit := do
  AcornTrackedFiles.runTrackedHelper ".." #["sync-config", "--clean", ".."] true
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

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [] => AcornGate.verify
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
