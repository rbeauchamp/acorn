/-
Copyright (c) 2026 acorn contributors.
Released under the MIT license as described in the repository LICENSE.
-/
import Lake
import Lake.Check.Axioms
import Lean.Replay
import Lean.Util.FoldConsts
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

/-- The package. Its default targets are the libraries that hold every Acorn theorem and every
definition those theorems are about, so they are the modules of Regula's claim: the modules
of the root package's default targets and each root-package module their imports reach
(Regula v0.12.0, `specification/README.md`, "The closed input"). The kernel replay
(`kernelReplay`) and `lake lint` import those modules into one environment, so at most one of
them can declare a top-level `main`: that one is `Bootstrap`'s, which `lean --run` interprets
before anything is built, and every executable's `main` lies in a module of the `Entry`
library, outside the claim. -/
package acorn where
  version := v!"0.1.0"
  -- Lake runs one compiler process per processor, and by default each process starts one
  -- thread per processor as well. Two threads per process bound the build at two compiler
  -- threads per processor. The argument is weak: it is no part of a build trace and does
  -- not change what any module elaborates to.
  weakLeanArgs := #["-j2"]
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`warningAsError, true⟩,
    ⟨`linter.missingDocs, true⟩,
    -- `debug.skipKernelTC` stays at its default, false, so the kernel typechecks every proof
    -- term the build adds, and the kernel replay of the proof verdict (`kernelReplay`)
    -- replays each proof of the claimed modules in Lean's kernel in any case.
    ⟨`linter.unusedVariables, true⟩,
    ⟨`linter.unnecessarySimpa, true⟩,
    ⟨`linter.deprecated, true⟩,
    -- Mathlib's standard linter set, with its header linter kept on for this license line and
    -- two linters that govern Mathlib's own repository off: the hash-command linter and the
    -- long-file linter.
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, true⟩,
    ⟨`weak.linter.style.header.license,
      "Released under the MIT license as described in the repository LICENSE."⟩,
    ⟨`weak.linter.hashCommand, false⟩,
    ⟨`weak.linter.style.longFile, .ofNat 0⟩,
  ]
  -- Regula's proof verdict on one build (`scripts/regula.sh`): `lake build --wfail`, the
  -- kernel replay `kernelReplay` in the place of `lake check --inadvisably-no-sandbox`, and
  -- `lake lint`. The one profile covers the whole
  -- claim: `standard-logical` admits `propext`, `Quot.sound` and `Classical.choice`, and the
  -- binary32 and binary64 operations of Lean's core float model, which the executing library
  -- uses, depend on `Classical.choice`.
  lintDriver := "regula/lint"
  lintDriverArgs := #["standard-logical"]

/-- Contracts about the executing definitions and their supporting mathematics.
Mathlib sets `requiresModuleSystem`, so Lake warns at each import of Mathlib from a file
without a `module` header. This library's files cannot be `module` files: they import the
executing definitions, which are not, and Lean refuses that import from a `module` file.
`allowNonModules` is Lake's opt-out of that warning alone; it is no Lean option and changes
no elaboration. -/
@[default_target]
lean_lib «AcornVerif» where
  globs := #[.andSubmodules `AcornVerif]
  allowNonModules := true

/-- Executable Acorn foundations.
Executable targets and native admission request their object files explicitly;
importing a proof or tooling leaf does not eagerly compile the whole library.
Native compilation includes the same admission definitions used by the proofs.
`Acorn.Decisions` registers the library's decision functions beside their Regula contracts.
It is the one module of this library that imports Regula's contract and registration types,
and no executable imports it. -/
@[default_target]
lean_lib «Acorn» where
  globs := #[.andSubmodules `Acorn]
  moreLeancArgs := nativeFloatFlags

/-- Native entry points embed provenance after their complete source dependency is built.
This bootstrap is a build/OS boundary, outside the current algorithm library. -/
@[default_target]
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
  root := `Entry.SwiftTdNative
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- Native consumer of current feature encoding and lifecycle transitions. -/
lean_exe «feature-native» where
  root := `Entry.FeatureNative
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- Native consumer of the current local prediction/control composition. -/
lean_exe «control-native» where
  root := `Entry.ControlNative
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- Native consumer of current option policy and persistent exploration definitions. -/
lean_exe «temporal-native» where
  root := `Entry.TemporalNative
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- Native consumer of the full current agent's exact initialization, prefix and observations. -/
lean_exe «agent-native» where
  root := `Entry.AgentNative
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- Minimal file-sync primitive; all checkpoint semantics remain in Lean. -/
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
lean_exe «acorn-core» where
  root := `Entry.AcornCore
  moreLeancArgs := nativeFloatFlags
  extraDepTargets := #[`checkpointSync, `nativeProvenance]

/-- Loopback observer and durable supervisor for the native core.
The core is named by its declaration, a facetless key: Lake resolves it through this
package to the store entry of a direct `acorn-core` request, so both share one link job. -/
lean_exe «acorn-viewer» where
  root := `Entry.AcornViewer
  moreLeancArgs := nativeFloatFlags
  extraDepTargets := #[`checkpointSync, `nativeProvenance]
  needs := #[«acorn-core»]

/-- Deterministic JavaScript kernel generated for the viewer. -/
lean_exe «browser-kernel» where
  root := `Entry.BrowserKernel
  moreLeancArgs := nativeFloatFlags

/-- Native current-agent checkpoint writer, receiver-bound loader and resume consumer. -/
lean_exe «checkpoint-native» where
  root := `Entry.CheckpointNative
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]
  extraDepTargets := #[`checkpointSync]

/-- Native consumer of current world, raw terrain and CLI admission. -/
lean_exe «world-native» where
  root := `Entry.WorldNative
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- The host of the Microduck's world: the agent's loop driven over three `nc` connections
to the simulated daemons, with telemetry on standard output. -/
lean_exe «microduck-host» where
  root := `Entry.MicroduckHost
  moreLeancArgs := #["-ffp-contract=off", "-fno-fast-math"]

/-- Generator-only certificate tool: proposes certificates for selecting properties of a
seed and prints what the checkers accept. The boundary audit keeps the agent composition,
the campaign runner and the comparator out of its import closure. That closure holds the
attempt protocol and campaign admission through the curriculum; the tool starts no attempt,
and no audit enforces that. -/
lean_exe «world-certificates» where
  root := `Entry.WorldCertificates
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

/-- The build bootstrap, which `scripts/lean.sh` interprets with `lean --run` before anything is
built, so its `main` stays in its own file: the one top-level `main` of the claim. The complete
local suite also compiles it. -/
@[default_target]
lean_lib «Bootstrap» where

/-- The names that maintained prose may cite from outside the project, which the corpus
audit admits, with the theorem that states what an admitted name is. -/
@[default_target]
lean_lib «AcornDocument» where

/-- The executables' roots. Each module declares the top-level `main` of one executable,
which applies the entry function of a claimed module and holds nothing else. The kernel
replay (`kernelReplay`) and `lake lint` import the claimed modules into one environment, where
Lean refuses two declarations of `main`, so these roots are no default target and no claimed
module imports one. -/
lean_lib «Entry» where
  globs := #[.andSubmodules `Entry]
  moreLeancArgs := nativeFloatFlags

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
`PartialBuildKey.fetchInCoreAux` (Lake, Lean v4.35.0; leanprover/lean4#15435) stores a
facet-qualified key under its target as written, while every other route stores that
facet under the target's resolved form, which names the package by its key name. The two
entries differ unless the key was written in that form. Whatever its form, the facet is
fetched from an asynchronous continuation, which races other fetches on the
unsynchronized build store. Either way a second job can run on the same output file.
A facetless key is resolved through its package and fetched synchronously, so it is the
form admitted. -/
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
A key outside `singleJobKey` in this package's configuration refuses the inventory.
The `needs` field marks an executable whose configuration names a target in `needs`: Lake
waits for that target before it reads any later build request, so the gate requests such an
entry last. -/
script acornTargets do
  let pkg ← getRootPackage
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

/-- The constants that Lean's kernel names by itself, so a replay holds them beside what the
claim needs: the list `lake comparator` roots for that reason (`primitiveTargets` and
`builtinTargets`, `Lake/CLI/Check.lean` of Lean v4.35.0), and the three axioms `lake check`
admits. -/
def kernelRoots : Array Lean.Name := #[`Nat.add, `Nat.sub, `Nat.mul, `Nat.pow, `Nat.gcd,
  `Nat.div, `Nat.mod, `Nat.beq, `Nat.ble, `Nat.land, `Nat.lor, `Nat.xor, `Nat.shiftLeft,
  `Nat.shiftRight, `String.ofList, `Char.ofNat, `List, `eagerReduce, `Nat, `String,
  `String.mk, `Char, `optParam, `autoParam, `semiOutParam, `outParam, `Quot, `propext,
  `Classical.choice, `Quot.sound]

/-- The axioms `lake check` admits (`standardAxioms`, `Lake/CLI/Check.lean` of Lean v4.35.0). -/
def admittedAxioms : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]

/-- The quotient constants the kernel adds itself when it adds `Quot`. The replay leaves them to
it and then compares them with the build's, as `leanchecker --from-export` does
(`LeanChecker.lean:68-90` of Lean v4.35.0). -/
def quotientParts : Array Lean.Name := #[`Quot.mk, `Quot.lift, `Quot.ind]

/-- What the kernel adds together with `n`: an inductive type with the other types of its block
and all their constructors, or `n` alone. -/
def replayUnit (map : Std.HashMap Lean.Name Lean.ConstantInfo) (n : Lean.Name) :
    Array Lean.Name := Id.run do
  let head := match map[n]? with
    | some (.ctorInfo v) => some v.induct
    | some (.inductInfo v) => some v.name
    | _ => none
  let some ind := head | return #[n]
  let some (.inductInfo v) := map[ind]? | return #[n]
  let mut out := #[]
  for t in v.all do
    out := out.push t
    if let some (.inductInfo w) := map[t]? then out := out ++ w.ctors.toArray
  return out

/-- What the kernel needs before `ci`: every constant its type or value names, and for an
inductive type, a constructor or a recursor, the types and constructors of its block, and
for `Quot`, `Eq`. A name
missing from the replayed environment makes the kernel refuse, never accept. -/
def replayNeeds (ci : Lean.ConstantInfo) : Array Lean.Name := Id.run do
  let mut out := ci.getUsedConstantsAsSet.foldl (·.push ·) #[]
  match ci with
  | .inductInfo v => out := out ++ v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => out := out.push v.induct
  | .recInfo v => out := out ++ v.all.toArray ++ (v.rules.map (·.ctor)).toArray
  -- `Quot.lift` and `Quot.ind` state `Eq`, which the kernel needs before `Quot`
  -- (`Lean/Replay.lean`).
  | .quotInfo _ => out := out.push `Eq
  | _ => pure ()
  return out

/-- The kernel replay of Acorn's proof verdict (`scripts/regula.sh`). Every constant of every
claimed module, with every constant it depends on, is replayed in Lean's kernel from an empty
environment by `Lean.Kernel.Environment.replay`.

A module is claimed as Regula v0.12.0 claims it: the modules of the root package's default
targets (Lake's `defaultModules` facet, which `lake check` exports) and every module their
imports reach whose `.olean` lies in the root package's library directory, each with the
constants its own module data lists. Every constant they name is replayed before them, so no
claimed constant is checked against one the kernel did not check. After the replay the quotient
constants are compared with the kernel's, and every axiom a replayed constant names must be one
of the three `lake check` admits, by Lake's own `usedAxioms`.

`lake check` replays every constant of the whole imported environment, Mathlib's included, from
an export it parses into memory; on Acorn's claim that check does not fit this machine. This
replay reads the build's `.olean` files in Lake's process and leaves out only the constants that
no claimed constant depends on, which no kernel check of a claimed constant reads. It leaves out
an unsafe or partial claimed constant, as `lake check` does: its export skips an unsafe constant
(`LeanExport/Basic.lean:255`) and Lean's replay skips both (`Lean/Replay.lean:183-185`). Regula's
RG1006 refuses each such claimed constant except the helper that Lean gives a terminating
recursive definition. -/
script kernelReplay do
  let ws ← getWorkspace
  let defaults ← ws.runBuild ws.root.defaultModules.fetch
  if defaults.isEmpty then
    IO.eprintln "kernel replay: the root package's default targets name no module"
    return 1
  Lean.initSearchPath ws.lakeEnv.lean.sysroot ws.augmentedLeanPath
  let env ← Lean.importModules (defaults.map fun m => { module := m.name }) {}
  let header := env.header
  let rootLib ← IO.FS.realPath ws.root.leanLibDir
  let mut claimed : Lean.NameSet := {}
  let mut seeds : Array Lean.Name := #[]
  for h : i in [0:header.moduleNames.size] do
    let olean ← IO.FS.realPath (← Lean.findOLean header.moduleNames[i])
    if rootLib.components.isPrefixOf olean.components then
      claimed := claimed.insert header.moduleNames[i]
      let some data := header.moduleData[i]?
        | IO.eprintln s!"kernel replay: no module data for {header.moduleNames[i]}"; return 1
      seeds := seeds ++ data.constNames
  for m in defaults do
    unless claimed.contains m.name do
      IO.eprintln s!"kernel replay: the default module {m.name} lies outside {rootLib}"
      return 1
  let constants := env.constants.map₁
  let toReplay := quotientParts.foldl (init := constants) (·.erase ·)
  let mut kept : Array Lean.Name := #[]
  let mut unchecked := 0
  for n in seeds do
    let some ci := toReplay[n]?
      | IO.eprintln s!"kernel replay: the environment holds no claimed constant {n}"; return 1
    if ci.isUnsafe || ci.isPartial then unchecked := unchecked + 1 else kept := kept.push n
  let claimedConstants := kept.size
  seeds := kernelRoots ++ kept
  let mut kenv := (← Lean.mkEmptyEnvironment).toKernelEnv
  let mut done : Lean.NameSet := quotientParts.foldl (·.insert ·) {}
  let mut expanding : Lean.NameSet := {}
  let mut stack : Array (Lean.Name × Bool) := seeds.reverse.map (·, false)
  let mut replayed := 0
  while !stack.isEmpty do
    let (n, ready) := stack.back!
    stack := stack.pop
    if done.contains n || (!ready && expanding.contains n) || !toReplay.contains n then continue
    let unit := replayUnit toReplay n
    if ready then
      let mut batch : Std.HashMap Lean.Name Lean.ConstantInfo := {}
      for x in unit do
        if let some c := toReplay[x]? then batch := batch.insert x c
      try
        kenv ← kenv.replay batch
      catch e =>
        IO.eprintln s!"kernel replay: Lean's kernel refuses {n}:\n{e}"
        return 1
      done := unit.foldl (·.insert ·) done
      replayed := replayed + batch.size
    else
      stack := stack.push (n, true)
      expanding := unit.foldl (·.insert ·) expanding
      for x in unit do
        if let some c := toReplay[x]? then
          for d in replayNeeds c do
            unless done.contains d || unit.contains d do stack := stack.push (d, false)
  for n in seeds do
    unless done.contains n do
      IO.eprintln s!"kernel replay: {n} was not replayed"
      return 1
  for q in #[`Quot] ++ quotientParts do
    if let some info := constants[q]? then
      unless kenv.find? q == some info do
        IO.eprintln s!"kernel replay: the kernel's {q} differs from the build's"
        return 1
  let checked := constants.filter fun n _ => done.contains n
  let used := Lake.Check.usedAxioms
    { constMap := checked, constOrder := checked.toArray.map (·.1) }
  let refused := used.filter fun (ax, _) => !admittedAxioms.contains ax
  unless refused.isEmpty do
    for (ax, ref) in refused do
      IO.eprintln s!"kernel replay: the axiom {ax}, which {ref} uses, is not admitted"
    return 1
  IO.println s!"kernel replay: Lean's kernel accepts {replayed} constants from an empty \
    environment, the {claimedConstants} constants of {claimed.size} claimed modules and every \
    constant they depend on, leaving out {unchecked} unsafe or partial claimed constants; \
    they use the axioms {used.toList.map (·.1)}"
  return 0

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

/-- Regula v0.12.0: the lint driver of the proof verdict, and the library `RegulaContract`, whose
contract and registration types the two decision registries import. -/
require regula from git
  "https://github.com/rbeauchamp/regula" @ "v0.12.0"

/-- Real-valued rounding theory about Lean core's float model. Only the proof
library's bridge module imports it; no executable library does. -/
require floatlib from git
  "https://github.com/lean-dojo/FloatLib" @ "1f5771b3e36a98f17fcac2c6d76aaa024b36aa37"

/-- Intent records, their adequacy obligations and the refinement link from an
implementation to its record. Only the proof library's intent bridge module imports it;
no executable library does. -/
require "lean-intent" from git
  "https://github.com/rbeauchamp/lean-intent" @ "30fe70d3bdeec8875eab718f38374a76a1df63c4"

/-- The artifacts of every module of `library` that the given sources import, read from
their own import lines so that each source stays the single owner of its imports. -/
def importedArtifacts (sources : Array System.FilePath) (library : String) :
    FetchM (Job Unit) := do
  let mut job : Job Unit := Job.nil
  for path in sources do
    for line in (← IO.FS.readFile path).splitOn "\n" do
      if line.startsWith s!"import {library}." then
        let name := ((line.drop 7).trimAscii.toString).toName
        let some mod ← findModule? name
          | error s!"{path} imports an unknown module: {name}"
        job := job.mix (← mod.leanArts.fetch)
  return job

/-- The FloatLib modules the proof bridge imports. Provisioning builds this target beside
Mathlib; FloatLib publishes no build cache, and verification must not compile a
dependency inside its deadline. -/
target floatlibBridge pkg : Unit :=
  importedArtifacts #[pkg.dir / "AcornVerif" / "FloatLibBridge.lean"] "FloatLib"

/-- The Regula interface modules the two decision registries import: the contract type and
the registration type. Provisioning builds this target beside `floatlibBridge`, for the
same reason. -/
target regulaInterface pkg : Unit :=
  importedArtifacts
    #[pkg.dir / "Acorn" / "Decisions.lean", pkg.dir / "AcornVerif" / "Decisions.lean"]
    "Regula"

/-- The lean-intent modules the intent bridge imports. Provisioning builds this target beside
`floatlibBridge`, for the same reason. -/
target leanIntentBridge pkg : Unit :=
  importedArtifacts #[pkg.dir / "AcornVerif" / "LeanIntentBridge.lean"] "LeanIntent"
