import Lake
open Lake DSL

private def stripNewline (text : String) : String :=
  (text.dropEndWhile fun c => c == '\n' || c == '\r').toString

private def isHexOid (value : String) : Bool :=
  (value.length == 40 || value.length == 64) &&
    value.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

private def admitTrackedHelper (dir : System.FilePath) (expectedPrefix : String) :
    IO System.FilePath := do
  let dirMeta ← dir.symlinkMetadata
  unless dirMeta.type == .dir do
    throw (IO.userError s!"expected directory for Git root: {dir}")
  let topOut ← IO.Process.output {
    cmd := "git", args := #["--no-optional-locks", "-C", dir.toString, "rev-parse", "--show-toplevel"],
    stdin := .null }
  unless topOut.exitCode == 0 do
    throw (IO.userError s!"git rev-parse --show-toplevel failed in {dir}: {topOut.stderr}")
  let prefixOut ← IO.Process.output {
    cmd := "git", args := #["--no-optional-locks", "-C", dir.toString, "rev-parse", "--show-prefix"],
    stdin := .null }
  unless prefixOut.exitCode == 0 do
    throw (IO.userError s!"git rev-parse --show-prefix failed in {dir}: {prefixOut.stderr}")
  let topStr := stripNewline topOut.stdout
  let prefixStr := stripNewline prefixOut.stdout
  unless prefixStr == expectedPrefix do
    throw (IO.userError s!"unexpected git prefix {prefixStr} in {dir}, expected {expectedPrefix}")
  let repoRoot := System.FilePath.mk topStr
  let expectedDir := if prefixStr.isEmpty then repoRoot
    else repoRoot / (prefixStr.dropEndWhile (· == '/')).toString
  unless (← IO.FS.realPath expectedDir) == (← IO.FS.realPath dir) do
    throw (IO.userError s!"git root mismatch for {dir}")
  let scriptsMeta ← (repoRoot / "scripts").symlinkMetadata
  unless scriptsMeta.type == .dir do
    throw (IO.userError "scripts is not a real directory")
  let helper := repoRoot / "scripts/tracked-files.sh"
  let helperMeta ← helper.symlinkMetadata
  unless helperMeta.type == .file do
    throw (IO.userError "scripts/tracked-files.sh is not a regular file")
  let stageOut ← IO.Process.output {
    cmd := "git",
    args := #["--no-optional-locks", "--literal-pathspecs", "-C", repoRoot.toString,
      "-c", "core.quotePath=false", "ls-files", "--stage", "-z", "--", "scripts/tracked-files.sh"],
    stdin := .null }
  unless stageOut.exitCode == 0 do
    throw (IO.userError s!"git ls-files failed for scripts/tracked-files.sh: {stageOut.stderr}")
  let records := (stageOut.stdout.splitOn (String.singleton (Char.ofNat 0))).filter (!·.isEmpty)
  let [record] := records | throw (IO.userError "scripts/tracked-files.sh is not tracked")
  let [metaPart, path] := record.splitOn "\t"
    | throw (IO.userError s!"malformed git ls-files record: {record}")
  let [mode, oid, stage] := metaPart.splitOn " "
    | throw (IO.userError s!"malformed git ls-files metadata: {metaPart}")
  unless (mode == "100644" || mode == "100755") && stage == "0" &&
      path == "scripts/tracked-files.sh" && isHexOid oid do
    throw (IO.userError "scripts/tracked-files.sh is not a stage-0 tracked regular file")
  return repoRoot

private def runTrackedHelper (repoRoot : System.FilePath) (args : Array String) : IO String := do
  let helper := repoRoot / "scripts/tracked-files.sh"
  let out ← IO.Process.output { cmd := helper.toString, args, stdin := .null }
  unless out.exitCode == 0 do
    throw (IO.userError (out.stderr ++ out.stdout).trimAscii.toString)
  return out.stdout

private def trackedEntriesIn (root : System.FilePath) (expectedPrefix : String) : IO (Array String) := do
  let repoRoot ← admitTrackedHelper root expectedPrefix
  let stdout ← runTrackedHelper repoRoot
    #["list-tracked", "--prefix", expectedPrefix, "--require-lean", root.toString]
  let paths := ((stdout.splitOn (String.singleton (Char.ofNat 0))).filter (!·.isEmpty)).toArray
  if paths.isEmpty then
    throw (IO.userError s!"tracked-files returned no tracked entries in {root}")
  return paths.qsort (· < ·)

private def ensureTrackedRegularIn (root : System.FilePath) (expectedPrefix : String)
    (rel : String) : IO Unit := do
  let repoRoot ← admitTrackedHelper root expectedPrefix
  discard (runTrackedHelper repoRoot #["admit-file", repoRoot.toString, expectedPrefix ++ rel])

private def moduleRelPath (root : Lean.Name) : String :=
  String.intercalate "/" (root.components.map (·.toString (escape := false))) ++ ".lean"

private def trackedExeRoot (entries : Array String) (root : Lean.Name) : IO Lean.Name := do
  let rel := moduleRelPath root
  unless entries.contains rel do
    throw (IO.userError s!"executable root is not a tracked regular file: {rel}")
  return root

private def trackedLibGlobs (entries : Array String) (root : Lean.Name) : Array Glob :=
  let prefixStr := Lean.Name.toString (escape := false) root
  let exactFile := prefixStr ++ ".lean"
  let subPrefix := prefixStr ++ "/"
  entries.filterMap fun rel =>
    if rel == exactFile || (rel.startsWith subPrefix && rel.endsWith ".lean") then
      let stem := (rel.dropEnd 5).toString
      some <| Glob.one ((stem.splitOn "/").foldl Lean.Name.str Lean.Name.anonymous)
    else none

private def trackedPackageEntries : Array String :=
  run_io (trackedEntriesIn __dir__ "lean/")

def nativeFloatFlags : Array String := #["-ffp-contract=off", "-fno-fast-math"]

def checkpointFlags : Array String := #["-std=c11", "-D_POSIX_C_SOURCE=200809L", "-D_DARWIN_C_SOURCE",
  "-Wall", "-Wextra", "-Werror", "-pedantic", "-O2"]

def nativeSources (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut files := #[]
  for rel in ← trackedEntriesIn root "lean/" do
    let path := root / rel
    if path.extension == some "lean" || path.extension == some "c" ||
        rel == "lean-toolchain" || rel == "lake-manifest.json" then
      files := files.push path
  return files.qsort (fun left right => left.toString < right.toString)

def nativeDigests (paths : Array System.FilePath) : IO (Array (System.FilePath × String)) := do
  if paths.isEmpty then return #[]
  for path in paths do
    if path.toString.contains '\n' then
      throw (IO.userError s!"native source path contains a newline: {path}")
  let output ← IO.Process.output {
    cmd := "openssl", args := #["dgst", "-sha256", "-r"] ++ paths.map (·.toString) }
  let lines := (output.stdout.splitOn "\n").toArray
  unless output.exitCode == 0 && lines.size == paths.size + 1 && lines.back? == some "" do
    throw (IO.userError s!"native source hashing failed: {output.stderr}")
  paths.mapIdxM fun i path => do
    let some line := lines[i]? | throw (IO.userError "missing native source digest")
    let digest := String.ofList (line.toList.take 64)
    unless digest.length == 64 &&
        digest.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) &&
        line == digest ++ " *" ++ path.toString do
      throw (IO.userError s!"malformed native source digest: {path}")
    return (path, digest)

def nativeDigest (path : System.FilePath) : IO String := do
  let #[(_, digest)] ← nativeDigests #[path]
    | throw (IO.userError "missing native source digest")
  return digest

package acorn where
  version := v!"0.1.0"
  weakLeanArgs := #["-j2"]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩,
    ⟨`weak.linter.hashCommand, false⟩,
    ⟨`weak.linter.style.longFile, .ofNat 0⟩,
  ]
  lintDriver := "regula/lint"
  lintDriverArgs := #["standard-logical"]

@[default_target]
lean_lib «AcornVerif» where
  roots := #[]
  globs := trackedLibGlobs trackedPackageEntries `AcornVerif
  allowNonModules := true

@[default_target]
lean_lib «Acorn» where
  roots := #[]
  globs := trackedLibGlobs trackedPackageEntries `Acorn
  moreLeancArgs := nativeFloatFlags

@[default_target]
lean_lib «NativeApp» where
  roots := #[]
  globs := trackedLibGlobs trackedPackageEntries `NativeApp
  extraDepTargets := #[`nativeProvenance, `checkpointSync]
  moreLeancArgs := nativeFloatFlags

def provenanceJob (pkg : Package) : FetchM (Job System.FilePath) := do
  ensureTrackedRegularIn pkg.dir "lean/" "Acorn/Host/AuditPins.lean"
  let sources ← nativeSources pkg.dir
  let pinOwner := pkg.dir / "Acorn/Host/AuditPins.lean"
  let root ← IO.FS.realPath (pkg.dir / "..")
  let sources ← (sources.mapM IO.FS.realPath : IO (Array System.FilePath))
  let sources := sources.qsort (fun left right => left.toString < right.toString)
  let dependencies ← sources.mapM fun path => inputBinFile path
  let compiler ← IO.Process.output { cmd := "lean", args := #["--version"] }
  let nativeCompiler ← IO.Process.output { cmd := "leanc", args := #["--version"] }
  let helperCompiler ← IO.Process.output { cmd := "cc", args := #["--version"] }
  unless compiler.exitCode == 0 && nativeCompiler.exitCode == 0 && helperCompiler.exitCode == 0 do
    error "native compiler identity unavailable"
  let settings := "acorn-lean-build-v1\n" ++ toString nativeFloatFlags ++ "\n" ++
    compiler.stdout ++ nativeCompiler.stdout ++ "checkpoint-sync\n" ++
    toString checkpointFlags ++ "\n" ++ helperCompiler.stdout
  let output := pkg.buildDir / "native-provenance.txt"
  buildFileAfterDep output (Job.collectArray dependencies) (fun files => do
    IO.FS.createDirAll pkg.buildDir
    let mut inventory := "acorn-lean-source-v2\n"
    for (path, digest) in ← nativeDigests files do
      let absolute ← IO.FS.realPath path
      unless absolute.toString.startsWith (root.toString ++ "/") do
        error "native source lies outside repository"
      inventory := inventory ++ digest ++ "  " ++
        String.ofList (absolute.toString.toList.drop (root.toString.length + 1)) ++ "\n"
    let scratch := pkg.buildDir / "native-source-inventory.txt"
    IO.FS.writeFile scratch inventory
    let source ← nativeDigest scratch
    let buildRecord := pkg.buildDir / "native-build-identity.txt"
    IO.FS.writeFile buildRecord (settings ++ "source=" ++ source ++ "\n")
    let build ← nativeDigest buildRecord
    let pinText ← IO.FS.readFile pinOwner
    let pinPrefix := "def declaredDigest : UInt64 := 0x"
    let [_, suffix] := pinText.splitOn pinPrefix
      | error "declared audit pin owner is ambiguous"
    let audit := String.ofList (suffix.toList.take 16)
    unless audit.length == 16 && suffix.toList[16]? == some '\n' &&
        audit.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
      error "declared audit pin is malformed"
    IO.FS.writeFile output (source ++ "\n" ++ build ++ "\n" ++ audit ++ "\n"))
    (extraDepTrace := pure (.ofHash ⟨hash (settings, sources.map (·.toString))⟩))

target nativeProvenance pkg : System.FilePath := provenanceJob pkg

lean_exe «swifttd-native» where
  root := run_io (trackedExeRoot trackedPackageEntries `Entry.SwiftTdNative)
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

lean_exe «feature-native» where
  root := run_io (trackedExeRoot trackedPackageEntries `Entry.FeatureNative)
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

lean_exe «control-native» where
  root := run_io (trackedExeRoot trackedPackageEntries `Entry.ControlNative)
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

lean_exe «temporal-native» where
  root := run_io (trackedExeRoot trackedPackageEntries `Entry.TemporalNative)
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

lean_exe «agent-native» where
  root := run_io (trackedExeRoot trackedPackageEntries `Entry.AgentNative)
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

target checkpointSync pkg : System.FilePath := do
  ensureTrackedRegularIn pkg.dir "lean/" "os/checkpoint-sync.c"
  let source ← inputTextFile (pkg.dir / "os/checkpoint-sync.c")
  let output := pkg.buildDir / "bin/checkpoint-sync"
  let compiler ← IO.Process.output { cmd := "cc", args := #["--version"] }
  unless compiler.exitCode == 0 do error "checkpoint compiler identity unavailable"
  buildFileAfterDep output source (fun source => do
    IO.FS.createDirAll (pkg.buildDir / "bin")
    proc { cmd := "cc", args := checkpointFlags ++ #[source.toString, "-o", output.toString] })
    (extraDepTrace := pure (.ofHash ⟨hash (compiler.stdout, checkpointFlags)⟩))

lean_exe «acorn-core» where
  root := run_io (trackedExeRoot trackedPackageEntries `Entry.AcornCore)
  moreLeancArgs := nativeFloatFlags
  extraDepTargets := #[`checkpointSync, `nativeProvenance]

lean_exe «acorn-viewer» where
  root := run_io (trackedExeRoot trackedPackageEntries `Entry.AcornViewer)
  moreLeancArgs := nativeFloatFlags
  extraDepTargets := #[`checkpointSync, `nativeProvenance]
  needs := #[«acorn-core»]

lean_exe «checkpoint-native» where
  root := run_io (trackedExeRoot trackedPackageEntries `Entry.CheckpointNative)
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]
  extraDepTargets := #[`checkpointSync]

lean_exe «world-native» where
  root := run_io (trackedExeRoot trackedPackageEntries `Entry.WorldNative)
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

lean_exe «microduck-host» where
  root := run_io (trackedExeRoot trackedPackageEntries `Entry.MicroduckHost)
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

lean_exe «world-certificates» where
  root := run_io (trackedExeRoot trackedPackageEntries `Entry.WorldCertificates)
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

lean_exe «theorem-count» where
  root := run_io (trackedExeRoot trackedPackageEntries `AcornTools.TheoremCount)
  supportInterpreter := true

lean_exe «lean-boundary-audit» where
  root := run_io (trackedExeRoot trackedPackageEntries `AcornTools.Boundary.Main)
  supportInterpreter := true

lean_exe «native-audit» where
  root := run_io (trackedExeRoot trackedPackageEntries `AcornTools.Native.Audit)

@[default_target]
lean_lib «Bootstrap» where
  roots := #[]
  globs := trackedLibGlobs trackedPackageEntries `Bootstrap

@[default_target]
lean_lib «AcornDocument» where
  roots := #[]
  globs := trackedLibGlobs trackedPackageEntries `AcornDocument

lean_lib «Entry» where
  roots := #[]
  globs := trackedLibGlobs trackedPackageEntries `Entry
  moreLeancArgs := nativeFloatFlags

lean_lib AcornTools where
  roots := #[]
  globs := trackedLibGlobs trackedPackageEntries `AcornTools

lean_exe «ownership-audit» where
  root := run_io (trackedExeRoot trackedPackageEntries `AcornTools.OwnershipAudit)
  supportInterpreter := true

lean_exe «acorn-gates» where
  root := run_io (trackedExeRoot trackedPackageEntries `AcornTools.Gate)

lean_exe «corpus-audit» where
  root := run_io (trackedExeRoot trackedPackageEntries `AcornTools.Corpus.Main)
  supportInterpreter := true

lean_exe «intent-check» where
  root := run_io (trackedExeRoot trackedPackageEntries `AcornTools.Intent)
  supportInterpreter := true

lean_exe «frame-check» where
  root := run_io (trackedExeRoot trackedPackageEntries `AcornTools.Frame)
  supportInterpreter := true

def singleJobKey (key : PartialBuildKey) : Bool :=
  match (key : BuildKey) with
  | .facet .. => false
  | _ => true

def configuredKeys (config : LeanConfig) (needs : Array PartialBuildKey) :
    Array PartialBuildKey :=
  needs ++ config.moreLinkObjs.map (·.key) ++ config.moreLinkLibs.map (·.key) ++
    config.dynlibs.map (·.key) ++ config.plugins.map (·.key)

script acornTargets do
  let pkg ← getRootPackage
  let tracked ← trackedEntriesIn pkg.dir "lean/"
  for exe in pkg.leanExes do
    let rel := moduleRelPath exe.config.root
    unless exe.config.srcDir == "." && tracked.contains rel do
      IO.eprintln s!"executable '{exe.name}' root is not a tracked regular file: {rel}"
      return 1
  let targets := #[(pkg.config.toLeanConfig, #[])] ++
    pkg.leanLibs.map (fun lib => (lib.config.toLeanConfig, lib.config.needs)) ++
    pkg.leanExes.map (fun exe => (exe.config.toLeanConfig, exe.config.needs))
  for (config, needs) in targets do
    if let some key := (configuredKeys config needs).find? (!singleJobKey ·) then
      IO.eprintln s!"facet-qualified build key '{key}' can give its target two Lake jobs"
      return 1
  let entries := pkg.leanExes.map fun exe => Lean.Json.mkObj [
    ("target", Lean.toJson (exe.name.toString false)),
    ("module", Lean.toJson exe.config.root.toString),
    ("needs", Lean.toJson !exe.config.needs.isEmpty)]
  IO.println (Lean.toJson entries).compress
  return 0

script intentLibraries do
  let pkg ← getRootPackage
  let libraries := pkg.defaultTargets.filter fun name => pkg.leanLibs.any (·.name == name)
  if libraries.isEmpty then
    IO.eprintln "the package has no default library"
    return 1
  IO.println (Lean.toJson (libraries.map (·.toString false))).compress
  return 0

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.36.0"

require regula from git
  "https://github.com/rbeauchamp/regula" @ "v0.13.1"

require floatlib from git
  "https://github.com/lean-dojo/FloatLib" @ "d24844f039320a024c7548f992920562d9a71a60"

require "lean-intent" from git
  "https://github.com/rbeauchamp/lean-intent" @ "v0.3.0"

def importedArtifacts (sources : Array System.FilePath) (library : String) :
    FetchM (Job Unit) := do
  let mut job : Job Unit := Job.nil
  for path in sources do
    for line in (← IO.FS.readFile path).splitOn "\n" do
      if line.startsWith s!"import {library}." then
        let name := ((line.drop 7).trimAscii.toString).toName
        let some mod ← findModule? name
          | error s!"{path} imports an unknown module: {name}"
        job := job.mix (← mod.irArts.fetch)
  return job

def importedNativeObjects (sources : Array System.FilePath) (library : String) :
    FetchM (Job Unit) := do
  let mut job : Job Unit := Job.nil
  for path in sources do
    for line in (← IO.FS.readFile path).splitOn "\n" do
      if line.startsWith s!"import {library}." then
        let name := ((line.drop 7).trimAscii.toString).toName
        let some mod ← findModule? name
          | error s!"{path} imports an unknown module: {name}"
        let imported ← (← mod.transImports.fetch).await
        for dependency in imported.push mod do
          job := job.mix ((← dependency.coExport.fetch).map fun _ => ())
  return job

def trackedSourceFiles (pkg : Package) (rels : Array String) : IO (Array System.FilePath) := do
  for rel in rels do
    ensureTrackedRegularIn pkg.dir "lean/" rel
  return rels.map (fun rel => pkg.dir / System.FilePath.mk rel)

target floatlibBridge pkg : Unit := do
  importedArtifacts (← trackedSourceFiles pkg #["AcornVerif/FloatLibBridge.lean"]) "FloatLib"

target regulaInterface pkg : Unit := do
  let registries ← trackedSourceFiles pkg #["Acorn/Decisions.lean", "AcornVerif/Decisions.lean"]
  let tools ← trackedSourceFiles pkg #["AcornTools/Theorems.lean"]
  let arts ← importedArtifacts (registries ++ tools) "Regula"
  let native ← importedNativeObjects tools "Regula"
  return arts.mix native

target leanIntentBridge pkg : Unit := do
  importedArtifacts
    (← trackedSourceFiles pkg #["AcornVerif/LeanIntentBridge.lean", "AcornTools/Intent.lean"])
    "LeanIntent"

target leanIntentNative pkg : Unit := do
  importedNativeObjects
    (← trackedSourceFiles pkg #["AcornVerif/LeanIntentBridge.lean", "AcornTools/Intent.lean"])
    "LeanIntent"
