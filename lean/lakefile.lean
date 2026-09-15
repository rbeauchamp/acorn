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

/-- Build-time hashing uses the provisioned OpenSSL; no runtime hashing process is needed. -/
def nativeDigest (path : System.FilePath) : IO String := do
  let output ← IO.Process.output { cmd := "openssl", args := #["dgst", "-sha256", "-r", path.toString] }
  let digest := String.ofList (output.stdout.toList.take 64)
  unless output.exitCode == 0 && digest.length == 64 &&
      digest.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw (IO.userError s!"native source hashing failed: {path}: {output.stderr}")
  return digest

/-- Scientific invocations bind the selected protocol's original bytes before execution. -/
def nativeProtocols (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut pending := #[]
  for entry in ← root.readDir do
    if (← entry.path.symlinkMetadata).type == .symlink then
      throw (IO.userError s!"study source is a symlink: {entry.path}")
    if (← entry.path.symlinkMetadata).type == .dir then
      let protocols := entry.path / "protocols"
      try
        unless (← protocols.symlinkMetadata).type == .dir do
          throw (IO.userError s!"protocol source is not a directory: {protocols}")
        pending := pending.push protocols
      catch error =>
        match error with
        | .noFileOrDirectory .. => pure ()
        | _ => throw error
  let mut files := #[]
  while !pending.isEmpty do
    let some directory := pending.back? | throw (IO.userError "protocol directory queue is empty")
    pending := pending.pop
    for entry in ← directory.readDir do
      if entry.fileName == ".DS_Store" then continue
      match (← entry.path.symlinkMetadata).type with
      | .dir => pending := pending.push entry.path
      | .file => files := files.push entry.path
      | _ => throw (IO.userError s!"protocol source is not regular: {entry.path}")
  return files.qsort (fun left right => left.toString < right.toString)

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

/-- Current executable Acorn foundations, separate from the historical evaluator.
Executable targets and native admission request their object files explicitly;
importing a proof or tooling leaf does not eagerly compile the whole library.
Native compilation includes the same admission definitions used by the proofs. -/
lean_lib «Acorn» where
  moreLeancArgs := nativeFloatFlags

/-- Preserved-data schemas and calculators, alongside the explicitly retained
historical evaluator. Native targets compile only their transitive imports. -/
lean_lib «AcornSpec»

/-- Study metadata admission and preserved-byte identity tooling. -/
lean_lib «AcornStudy»

/-- Native entry points embed provenance after their complete source dependency is built.
This bootstrap is a build/OS boundary, outside the current algorithm library. -/
lean_lib «NativeApp» where
  extraDepTargets := #[`nativeProvenance, `checkpointSync]
  moreLeancArgs := nativeFloatFlags

meta if get_config? privateEvidence == some "true" then
  /-- Private scientific adapters have a separate compile-bound protocol dependency. -/
  lean_lib «NativeResearch» where
    extraDepTargets := #[`researchProvenance, `checkpointSync]
    moreLeancArgs := nativeFloatFlags

/-- Raw source identity and actual toolchain identity embedded into native entry points.
The inventory covers every Lean/C source in this package and the declared audit pin owner.
Digests establish byte identity, not authenticity or a correctness theorem. -/
def provenanceJob (pkg : Package) (research : Bool) : FetchM (Job System.FilePath) := do
  let sources ← nativeSources pkg.dir
  let pinOwner := pkg.dir / "Acorn/Host/AuditPins.lean"
  let protocols ← if research then nativeProtocols (pkg.dir / "../studies") else pure #[]
  let sources := sources ++ #[pkg.dir / "../viewer/static/index.html", pkg.dir / "../verification-profile"] ++ protocols
  let outputPrefix := if research then "research" else "native"
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
  let output := pkg.buildDir / (outputPrefix ++ "-provenance.txt")
  buildFileAfterDep output (Job.collectArray dependencies) (fun files => do
    IO.FS.createDirAll pkg.buildDir
    let mut inventory := "acorn-lean-source-v2\n"
    for path in files do
      let absolute ← IO.FS.realPath path
      unless absolute.toString.startsWith (root.toString ++ "/") do
        error "native source lies outside repository"
      inventory := inventory ++ (← nativeDigest path) ++ "  " ++
        String.ofList (absolute.toString.toList.drop (root.toString.length + 1)) ++ "\n"
    let scratch := pkg.buildDir / (outputPrefix ++ "-source-inventory.txt")
    IO.FS.writeFile scratch inventory
    let source ← nativeDigest scratch
    let buildRecord := pkg.buildDir / (outputPrefix ++ "-build-identity.txt")
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

/-- Shared application provenance has no dependency on historical study records. -/
target nativeProvenance pkg : System.FilePath := provenanceJob pkg false

/-- Private scientific provenance includes every original protocol before compilation. -/
target researchProvenance pkg : System.FilePath := provenanceJob pkg true

meta if get_config? privateEvidence == some "true" then
  /-- Native dossier admission, integrity, indexing and canonical reproduction. -/
  lean_exe «study-tool» where
    root := `AcornStudy.Main

meta if get_config? privateEvidence == some "true" then
  /-- Untrusted development tool around the specification: the probe, for
  step-level divergence localization against the Rust binary. Never part of any
  theorem's trusted base. -/
  lean_exe «specprobe» where
    root := `AcornSpec.Probe

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

meta if get_config? privateEvidence == some "true" then
  /-- Private scientific execution uses compile-bound protocols and the same algorithm owners. -/
  lean_exe «acorn-research» where
    root := `NativeResearch.Main
    moreLeancArgs := nativeFloatFlags
    extraDepTargets := #[`checkpointSync, `researchProvenance]

/-- Loopback observer and durable supervisor for the native core. -/
lean_exe «acorn-viewer» where
  root := `NativeApp.Viewer
  moreLeancArgs := nativeFloatFlags
  extraDepTargets := #[`checkpointSync, `nativeProvenance]
  needs := #[PartialBuildKey.mk (.targetFacet .anonymous `«acorn-core» `exe)]

/-- Deterministic observer calculation source for the retained Rust host. -/
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

meta if get_config? privateEvidence == some "true" then
  /-- Offline calculator over the baseline's preserved, untrusted shard literals.
  It compares the registered result with the original report before printing it. -/
  lean_exe «agent-baseline» where
    root := `AcornSpec.AgentBaselineMain

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

meta if get_config? privateEvidence == some "true" then
  /-- Private dossier and canonical-publication admission. -/
  lean_exe «study-corpus-audit» where
    root := `AcornTools.Corpus.Studies
    supportInterpreter := true

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

meta if get_config? privateEvidence == some "true" then
  /-- The registered intra-option-credit analysis runner: evaluates the registered
  functional `AcornSpec.intraOptionCreditResult` over the recorded rows twins.
  A calculator for the registered definition; never part of any theorem's
  trusted base. -/
  lean_exe «intra-option-credit» where
    root := `AcornSpec.IntraOptionCreditMain

meta if get_config? privateEvidence == some "true" then
  /-- The registered derived-exploration-rate analysis runner: evaluates the registered
  functional `AcornSpec.derivedExplorationRateResult` over the recorded rows twins.
  A calculator for the registered definition; never part of any theorem's
  trusted base. -/
  lean_exe «derived-exploration-rate» where
    root := `AcornSpec.DerivedExplorationRateMain

meta if get_config? privateEvidence == some "true" then
  /-- The registered stomp-planning analysis runner: evaluates the registered
  functional `AcornSpec.stompPlanningResult` over the recorded rows twins.
  A calculator for the registered definition; never part of any theorem's
  trusted base. -/
  lean_exe «stomp-planning» where
    root := `AcornSpec.StompPlanningMain

meta if get_config? privateEvidence == some "true" then
  /-- Exact-rational paired analysis of the differential-control protocol. -/
  lean_exe «average-reward-control» where
    root := `AcornSpec.AverageRewardControlMain

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.33.0"

meta if get_config? privateEvidence == some "true" then
  /-- Read-only admission of the prepared publication mapping. -/
  lean_exe «publication-audit» where
    root := `AcornTools.Corpus.Publication
    supportInterpreter := true
