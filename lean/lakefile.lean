/-
Copyright (c) 2026 acorn contributors.
Released under the MIT license as described in the repository LICENSE.
-/
import Lake
open Lake DSL

/-- Strict operation settings shared by the executing library and native application. -/
def nativeFloatFlags : Array String := #["-ffp-contract=off", "-fno-fast-math"]

/-- Complete settings of the minimal native persistence primitive. -/
def checkpointFlags : Array String := #["-std=c11", "-D_POSIX_C_SOURCE=200809L", "-D_DARWIN_C_SOURCE",
  "-Wall", "-Wextra", "-Werror", "-pedantic", "-O2"]

/-- The native build inventory rejects links and nonregular source entries. -/
partial def nativeSources (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut files := #[]
  for entry in ← root.readDir do
    if entry.fileName == ".lake" || entry.fileName == "lake-packages" ||
        entry.fileName == ".DS_Store" then continue
    let metadata ← entry.path.symlinkMetadata
    match metadata.type with
    | .dir => files := files ++ (← nativeSources entry.path)
    | .file =>
      if entry.path.extension == some "lean" || entry.path.extension == some "c" ||
          entry.fileName == "lean-toolchain" || entry.fileName == "lake-manifest.json" then
        files := files.push entry.path
    | _ => throw (IO.userError s!"native source is not a regular entry: {entry.path}")
  return files.qsort (fun left right => left.toString < right.toString)

/-- Hash each source with provisioned OpenSSL in one process. Admit exactly one
SHA-256 result per input, in order and with the complete matching filename.
Newline-containing paths cannot be represented in the source inventory. -/
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

/-- Singleton hashing shares the source batch's complete output admission. -/
def nativeDigest (path : System.FilePath) : IO String := do
  let #[(_, digest)] ← nativeDigests #[path]
    | throw (IO.userError "missing native source digest")
  return digest

package acorn where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`linter.missingDocs, true⟩,
    -- The kernel must typecheck every proof term; never skip it.
    ⟨`debug.skipKernelTC, false⟩,
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩,
    -- Mathlib's standard linter set, with its header linter kept on for this license line.
    -- Regula's RG2006 (https://rbeauchamp.github.io/regula/v/0.4.3/rules/RG2006/) requires the
    -- two Mathlib-repository linters below to be off.
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, true⟩,
    ⟨`weak.linter.style.header.license,
      "Released under the MIT license as described in the repository LICENSE."⟩,
    ⟨`weak.linter.hashCommand, false⟩,
    ⟨`weak.linter.style.longFile, .ofNat 0⟩,
  ]
  lintDriver := "regula/lint"

/-- Contracts about the executing definitions and their supporting mathematics. -/
lean_lib «AcornVerif» where
  globs := #[.andSubmodules `AcornVerif]

/-- Executable Acorn foundations.
Executable targets and native admission request their object files explicitly;
importing a proof or tooling leaf does not eagerly compile the whole library.
Native compilation includes the same admission definitions used by the proofs. -/
lean_lib «Acorn» where
  globs := #[.andSubmodules `Acorn]
  moreLeancArgs := nativeFloatFlags

/-- Native entry points embed provenance after their complete source dependency is built.
This bootstrap is a build/OS boundary, outside the current algorithm library. -/
lean_lib «NativeApp» where
  globs := #[.andSubmodules `NativeApp]
  extraDepTargets := #[`nativeProvenance, `checkpointSync]
  moreLeancArgs := nativeFloatFlags

/-- Raw source identity and actual toolchain identity embedded into native entry points.
The inventory covers every Lean/C source in this package and the declared audit pin owner.
Digests establish byte identity, not authenticity or a correctness theorem. -/
def provenanceJob (pkg : Package) : FetchM (Job System.FilePath) := do
  let sources ← nativeSources pkg.dir
  let pinOwner := pkg.dir / "Acorn/Host/AuditPins.lean"
  let sources := sources ++ #[pkg.dir / "../viewer/static/index.html"]
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

/-- Complete source and compiler identity embedded in the application. -/
target nativeProvenance pkg : System.FilePath := provenanceJob pkg

/-- Native consumer of the current proof-bearing learner, with the same
strict floating-operation options as the executing library. -/
lean_exe «swifttd-native» where
  root := `Acorn.SwiftTdDriver
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- Native consumer of current feature encoding and lifecycle transitions. -/
lean_exe «feature-native» where
  root := `Acorn.FeatureDriver
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- Native consumer of the current local prediction/control composition. -/
lean_exe «control-native» where
  root := `Acorn.ControlDriver
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- Native consumer of current option policy and persistent exploration definitions. -/
lean_exe «temporal-native» where
  root := `Acorn.TemporalDriver
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- Native consumer of the full current agent's exact initialization, prefix and observations. -/
lean_exe «agent-native» where
  root := `Acorn.AgentDriver
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- Minimal POSIX file-sync primitive; all checkpoint semantics remain in Lean. -/
target checkpointSync pkg : System.FilePath := do
  let source ← inputTextFile (pkg.dir / "os/checkpoint-sync.c")
  let output := pkg.buildDir / "bin/checkpoint-sync"
  let compiler ← IO.Process.output { cmd := "cc", args := #["--version"] }
  unless compiler.exitCode == 0 do error "checkpoint compiler identity unavailable"
  buildFileAfterDep output source (fun source => do
    IO.FS.createDirAll (pkg.buildDir / "bin")
    proc { cmd := "cc", args := checkpointFlags ++ #[source.toString, "-o", output.toString] })
    (extraDepTrace := pure (.ofHash ⟨hash (compiler.stdout, checkpointFlags)⟩))

/-- The viewer-owned current native agent stream, with the same executable definitions as its proofs. -/
@[default_target]
lean_exe «acorn-core» where
  root := `NativeApp.Main
  moreLeancArgs := nativeFloatFlags
  extraDepTargets := #[`checkpointSync, `nativeProvenance]

/-- Loopback observer and durable supervisor for the native core.
The core is named by its declaration, a facetless key: Lake resolves it through this
package to the store entry of a direct `acorn-core` request, so both share one link job. -/
lean_exe «acorn-viewer» where
  root := `NativeApp.Viewer
  moreLeancArgs := nativeFloatFlags
  extraDepTargets := #[`checkpointSync, `nativeProvenance]
  needs := #[«acorn-core»]

/-- Deterministic JavaScript kernel generated for the viewer. -/
lean_exe «browser-kernel» where
  root := `NativeApp.BrowserKernel
  moreLeancArgs := nativeFloatFlags

/-- Native current-agent checkpoint writer, receiver-bound loader and resume consumer. -/
lean_exe «checkpoint-native» where
  root := `Acorn.Host.CheckpointDriver
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]
  extraDepTargets := #[`checkpointSync]

/-- Native consumer of current world, raw terrain and CLI admission. -/
lean_exe «world-native» where
  root := `Acorn.WorldDriver
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- Inventory theorem declarations from compiled project modules, scoped by
the compiler's owning-module index rather than source text or name prefixes. -/
lean_exe «theorem-count» where
  root := `AcornTools.TheoremCount
  supportInterpreter := true

/-- Boundary admission entry, isolated from application compilation. -/
lean_exe «lean-boundary-audit» where
  root := `AcornTools.Boundary.Main
  supportInterpreter := true

/-- Inspect the actual native compiler flags, primitives and execution routes. -/
lean_exe «native-audit» where
  root := `AcornTools.Native.Audit

/-- Interpreted build bootstrap is also compiled by the complete local suite. -/
lean_lib «Bootstrap»

/-- Reviewed build and verification tools, separate from application libraries. -/
lean_lib AcornTools where
  globs := #[.andSubmodules `AcornTools]

/-- Check discovered sources, evaluated executable roots and required proof links. -/
lean_exe «ownership-audit» where
  root := `AcornTools.OwnershipAudit
  supportInterpreter := true

/-- Offline ordinary verification orchestration. -/
lean_exe «acorn-gates» where
  root := `AcornTools.Gate

/-- Source-only maintained-corpus admission. -/
lean_exe «corpus-audit» where
  root := `AcornTools.Corpus.Main
  supportInterpreter := true

/-- A sufficient condition for a configured build key to share its target's one Lake job.
`PartialBuildKey.fetchInCoreAux` (Lake, Lean v4.34.0; leanprover/lean4#15435) stores a
facet-qualified key under its target as written, while every other route stores that
facet under the target's resolved form, which names the package by its key name. The two
entries differ unless the key was written in that form. Whatever its form, the facet is
fetched from an asynchronous continuation, which races other fetches on the
unsynchronized build store. Either way a second job can run on the same output file.
A facetless key is resolved through its package and fetched synchronously. -/
def singleJobKey (key : PartialBuildKey) : Bool :=
  match (key : BuildKey) with
  | .facet .. => false
  | _ => true

/-- Every key a Lean configuration hands to Lake's partial-key fetch. -/
def configuredKeys (config : LeanConfig) (needs : Array PartialBuildKey) :
    Array PartialBuildKey :=
  needs ++ config.moreLinkObjs.map (·.key) ++ config.moreLinkLibs.map (·.key) ++
    config.dynlibs.map (·.key) ++ config.plugins.map (·.key)

/-- Emit the evaluated Lake executable inventory for ownership admission.
The gate compares this with compiled `main` owners before accepting a build.
A key outside `singleJobKey` in this package's configuration refuses the inventory. -/
script acornTargets do
  let pkg ← getRootPackage
  let keys := configuredKeys pkg.config.toLeanConfig #[] ++
    pkg.leanLibs.flatMap (fun lib => configuredKeys lib.config.toLeanConfig lib.config.needs) ++
    pkg.leanExes.flatMap (fun exe => configuredKeys exe.config.toLeanConfig exe.config.needs)
  if let some key := keys.find? (!singleJobKey ·) then
    IO.eprintln s!"facet-qualified build key '{key}' can give its target two Lake jobs"
    return 1
  let entries := pkg.leanExes.map fun exe => Lean.Json.mkObj [
    ("target", Lean.toJson (exe.name.toString false)),
    ("module", Lean.toJson exe.config.root.toString)]
  IO.println (Lean.toJson entries).compress
  return 0

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.34.0"

require regula from git
  "https://github.com/rbeauchamp/regula" @ "v0.4.3"

/-- Real-valued rounding theory about Lean core's float model. Only the proof
library's bridge module imports it; no executable library does. -/
require floatlib from git
  "https://github.com/lean-dojo/FloatLib" @ "1e83f09ed8c41a953cf8f93d26c210778177b94a"

/-- The FloatLib modules the proof bridge imports, read from the bridge's own import
lines so that it stays their single owner. Provisioning builds this target beside
Mathlib; FloatLib publishes no build cache, and verification must not compile a
dependency inside its deadline. -/
target floatlibBridge pkg : Unit := do
  let source ← IO.FS.readFile (pkg.dir / "AcornVerif" / "FloatLibBridge.lean")
  let mut job : Job Unit := Job.nil
  for line in source.splitOn "\n" do
    if line.startsWith "import FloatLib." then
      let name := ((line.drop 7).trimAscii.toString).toName
      let some mod ← findModule? name
        | error s!"the FloatLib bridge imports an unknown module: {name}"
      job := job.mix (← mod.leanArts.fetch)
  return job
