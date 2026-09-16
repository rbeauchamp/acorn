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
  ]
  weakLeanArgs := #[
    "-Dweak.linter.mathlibStandardSet=true",
    "-Dweak.linter.style.header=true",
    "-Dweak.linter.style.header.license=Released under the MIT license as described in the repository LICENSE.",
  ]

lean_lib «AcornVerif»

/-- Executable Acorn foundations.
Executable targets and native admission request their object files explicitly;
importing a proof or tooling leaf does not eagerly compile the whole library.
Native compilation includes the same admission definitions used by the proofs. -/
lean_lib «Acorn» where
  moreLeancArgs := nativeFloatFlags

/-- Native entry points embed provenance after their complete source dependency is built.
This bootstrap is a build/OS boundary, outside the current algorithm library. -/
lean_lib «NativeApp» where
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
    let pinPrefix := "def derivedDigest : UInt64 := 0x"
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

/-- Loopback observer and durable supervisor for the native core. -/
lean_exe «acorn-viewer» where
  root := `NativeApp.Viewer
  moreLeancArgs := nativeFloatFlags
  extraDepTargets := #[`checkpointSync, `nativeProvenance]
  needs := #[PartialBuildKey.mk (.targetFacet .anonymous `«acorn-core» `exe)]

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
lean_lib AcornTools

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

/-- Emit the evaluated Lake executable inventory for ownership admission.
The gate compares this with compiled `main` owners before accepting a build. -/
script acornTargets do
  let pkg ← getRootPackage
  let entries := pkg.leanExes.map fun exe => Lean.Json.mkObj [
    ("target", Lean.toJson (exe.name.toString false)),
    ("module", Lean.toJson exe.config.root.toString)]
  IO.println (Lean.toJson entries).compress
  return 0

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.0"
