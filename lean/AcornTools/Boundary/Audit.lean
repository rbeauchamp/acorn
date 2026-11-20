/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.ModuleInventory
import AcornTools.Ownership
import AcornTools.Boundary.Departures

/-!
# Admission of the current Lean execution boundary

Source is parsed with the pinned compiler's trusted parser environment before
project extensions are loaded. Current sources cannot define parser/elaborator
extensions or spell a native replacement. Compiled metadata then checks actual module
ownership, including private/generated declarations and transitive imports.
The Regula audit of the claimed libraries, not this tool, checks compiled declarations
for project axioms, proof holes, compiler-trusting proofs and `unsafe` or `partial`
definitions; the theorem inventory refuses a compiled native replacement.

Source admission covers every project module outside the tools: the executing sources and
the proof sources divide them (`proofSide`). Before anything else is built it also requires
that no gate tool, and no module of the documentation site's own tooling, imports a module of
the project from outside the owner's paths (`toolImports`), so the code that judges a change is
elaborated and linked without the change's own modules.

This verification tool and the pinned Lean/Init toolchain are trusted. The gate
does not prove compiler correctness or the truth of a provenance declaration.
-/
namespace AcornBoundaryAudit
open Lean

/-- Explicit composition roots may join learned and declared code. -/
def compositionRoots : Array Name := #[`Acorn, `Acorn.SwiftTdDriver, `Acorn.FeatureDriver, `Acorn.WorldDriver, `Acorn.ControlDriver, `Acorn.TemporalDriver, `Acorn.AgentDriver]

/-- The registration leaf of the executing library states contracts about executing
definitions. No module imports it, so no entry point links what it declares. It has its own
import and command admission below. -/
def registry (name : Name) : Bool := name == AcornModuleInventory.decisionRegistry

/-- The executables' roots: each declares the top-level `main` of one executable. -/
def entry (name : Name) : Bool := (`Entry).isPrefixOf name

/-- Executing application sources, their shared constant leaf and the executables' roots. -/
def governed (name : Name) : Bool := ((`Acorn).isPrefixOf name ||
  (`NativeApp).isPrefixOf name || entry name) && !registry name

/-- Mathematical proofs have separate import admission. -/
def proofOwner (name : Name) : Bool := (`AcornVerif).isPrefixOf name

/-- The project modules that proof-source admission admits: the proof library, and the decision
registry, which states contracts. Source admission admits every other project module, so the two
admissions divide the project modules between them and none lies outside both. -/
def proofSide (name : Name) : Bool := proofOwner name || registry name

/-- Native entry/resource owners and the executables' roots are checked as host code, never
learned algorithms. -/
def nativeBootstrap (name : Name) : Bool := (`NativeApp).isPrefixOf name || entry name

/-- Host and declared modules are quarantined by their owning module, not namespaces. -/
def quarantined (name : Name) : Bool :=
  (`Acorn.Host).isPrefixOf name || (`Acorn.Handcrafted).isPrefixOf name

/-- Every other current module is learned, including any newly added nested module. -/
def learned (name : Name) : Bool :=
  (`Acorn).isPrefixOf name && !quarantined name && !compositionRoots.contains name

/-- Declared modules bound to the grid world: its channel layout, its signals and its
interface instance. -/
def gridOwners : Array Name := #[`Acorn.Handcrafted.Observation, `Acorn.Handcrafted.Cumulants,
  `Acorn.Handcrafted.GridWorld]

/-- The declared module bound to the Microduck world: its interface instance with its
adapter. -/
def microduckOwners : Array Name := #[`Acorn.Handcrafted.Microduck]

/-- Declared modules bound to one world. -/
def worldOwners : Array Name := gridOwners ++ microduckOwners

/-- Every other declared module imports no world: the composed agent, its profiles and its
world-independent declarations. A newly added declared module is world-independent until
it is listed as an owner of a world. -/
def worldIndependent (name : Name) : Bool :=
  (`Acorn.Handcrafted).isPrefixOf name && !worldOwners.contains name

/-- The proof module that states Regula contracts whose proofs need the proof library. It
alone among the proof modules imports Regula's contract type. -/
def proofContracts : Name := `AcornVerif.Decisions

/-- The single proof module that imports the pinned FloatLib dependency. Other proof
modules reach FloatLib's theorems through it; no executing module can. -/
def floatLibBridge : Name := `AcornVerif.FloatLibBridge

/-- The single proof module that imports the pinned lean-intent dependency. The intent records
reach lean-intent's declarations through it; no executing module can. -/
def leanIntentBridge : Name := `AcornVerif.LeanIntentBridge

/-- Owners of the generator-only certificate tool. -/
def generatorOnly (name : Name) : Bool :=
  #[`Acorn.Host.Certificate, `Acorn.Host.CertificateSearch, `Acorn.Host.CertificateDriver].contains name

/-- What a generator-only owner may not import, directly or transitively: the agent
composition, the campaign runner and the random-policy comparator. The certificate tool
therefore cannot construct or run any of them. -/
def generatorExcluded (imported : Name) : Bool :=
  (`Acorn.Handcrafted).isPrefixOf imported ||
    #[`Acorn.Host.Runner, `Acorn.Host.Baseline].contains imported

/-- Only host/composition owners may use the pinned standard containers and IO support.
A world-independent declared module reaches learned modules and its own kind only, so
the composed agent cannot name a type of a host or of a world, directly or through an
import.
Proof imports name their actual dependencies; Mathlib and FloatLib umbrella imports
needlessly load an entire library or tactic collection into each compiler process.
FloatLib modules are admitted for the bridge alone, lean-intent modules for the intent bridge
alone, and Regula's contract type for the proof module that states contracts. The decision registry imports
executing modules and Regula's two registration interfaces, the contract type and the
registration type. No module imports the registry, so neither enters an executable's or a
proof's import closure. -/
def importAllowed (owner imported : Name) : Bool :=
  if (`Init).isPrefixOf imported then true
  else if registry imported then false
  else if registry owner then
    (`Acorn).isPrefixOf imported || #[`Regula.Contract, `Regula.Decision].contains imported
  else if generatorOnly owner && generatorExcluded imported then false
  else if proofOwner owner then
    !#[`Mathlib, `Mathlib.Tactic, `FloatLib].contains imported &&
      (#[`Acorn, `AcornVerif, `Mathlib, `Lean, `Std].any (·.isPrefixOf imported) ||
        (owner == floatLibBridge && (`FloatLib).isPrefixOf imported) ||
        (owner == leanIntentBridge && (`LeanIntent).isPrefixOf imported) ||
        (owner == proofContracts && imported == `Regula.Contract))
  else if nativeBootstrap owner then
    (`NativeApp).isPrefixOf imported || (`Acorn).isPrefixOf imported || (`Std).isPrefixOf imported
  -- A module of no library named above, such as `AcornDocument`, imports only `Init` modules.
  else if !(`Acorn).isPrefixOf owner then false
  else if owner == `Acorn.Constants then false
  else if (`Std).isPrefixOf imported then
    (`Acorn.Host).isPrefixOf owner || compositionRoots.contains owner
  else if !(`Acorn).isPrefixOf imported then false
  else if learned owner then learned imported
  else if worldIndependent owner then learned imported || worldIndependent imported
  else true

/-- Errors include both the source owner and rejected capability. -/
def reject {α : Type} (owner : Name) (reason : String) : IO α :=
  throw (IO.userError s!"Lean boundary {owner}: {reason}")

/-- A small reviewed attribute domain has no native replacement or metaprogram registration. -/
def allowedAttributes : Array Name := #[`simp, `inline, `noinline, `reducible, `irreducible]

/-- These options change proof resource limits, never kernel checking or parser admission. The
list holds at every depth of a source: for the command, and for an option set before a term, a
tactic sequence or a grind sequence (`inspectOption`). An option that a dependency's own macro or
elaborator sets is that dependency's code and is not scanned. -/
def allowedOptions : Array Name := #[`maxRecDepth, `maxHeartbeats, `exponentiation.threshold]

/-- The option that a form beginning with the atom `set_option` sets is a listed one, or in a
proof source the linter of evaluating commands. Lean reads the option's name from the form's
second part (`Lean.Elab.elabSetOption`), so a form whose second part is no identifier is
refused. -/
def inspectOption (owner : Name) (form : Syntax) : IO Unit := do
  unless form[1].isIdent do reject owner "an option setting that names no option"
  let option := form[1].getId
  unless allowedOptions.contains option || (proofOwner owner && option == `linter.hashCommand) do
    reject owner s!"unreviewed option {option}"

/-- Only these admitted host boundaries may create or inspect native subprocesses. -/
def processOwners : Array Name := #[`Acorn.Host.Checkpoint.IO, `Acorn.Host.Control,
  `Acorn.Host.Viewer.RunDirectory, `Acorn.Host.Viewer.ProcessOwner,
  `Acorn.Host.Viewer.NativeResources, `Acorn.Host.Microduck.Transport, `NativeApp.Viewer]

/-- Native effects cannot be smuggled into learned modules through Init aliases. -/
def capabilityAllowed (owner dependency : Name) : Bool :=
  if owner == `Acorn.Host.Viewer.ProcessOwner &&
      (`IO.Process.Child.kill).isPrefixOf dependency then false
  else if (`IO.Process).isPrefixOf dependency then processOwners.contains owner
  else if (`Acorn.Host.Viewer).isPrefixOf owner && owner != `Acorn.Host.Viewer.RunDirectory &&
      (#[`IO.FS.writeFile, `IO.FS.writeBinFile, `IO.FS.createDir, `IO.FS.createDirAll,
        `IO.FS.removeFile, `IO.FS.removeDir, `IO.FS.removeDirAll, `IO.FS.rename,
        `IO.FS.Handle.mk, `IO.FS.withFile, `IO.FS.createTempFile, `IO.FS.createTempDir,
        `IO.setAccessRights].any (·.isPrefixOf dependency)) then false
  else if (`Acorn.Host.Viewer).isPrefixOf owner &&
      (#[`IO.FS.Handle.write, `IO.FS.Handle.putStr, `IO.FS.Handle.putStrLn,
        `IO.FS.Handle.truncate].any (·.isPrefixOf dependency)) then
    owner == `Acorn.Host.Viewer.RunDirectory || owner == `Acorn.Host.Viewer.ProcessOwner
  else if learned owner then
    !(#[`IO, `BaseIO, `EIO].any (·.isPrefixOf dependency))
  else true

/-- Reserved syntax capabilities are rejected even when nested in proof terms. -/
def forbiddenWords : Array String := #["unsafe", "partial", "meta", "axiom", "sorry", "admit",
  "native_decide", "run_tac", "run_elab", "by_elab", "extern", "implemented_by", "csimp",
  "simproc", "builtin_simproc", "elab", "macro", "initialize", "builtin_initialize", "_unsafe_rec"]

/-- The files a source may include as text while it is elaborated (`include_str`), each with the
one module that includes it and the path as that module writes it, relative to its own file: the
viewer's page, and the three records the Lake configuration's provenance target writes into the
build directory. What is admitted is the form and its string literal: every other inclusion is
refused, and so is one whose path is not a string literal. The file Lean reads when it elaborates
the term is what its elaborator computes from that literal, as a file path, and an instance
declared in the including module could change that computation. This is accepted: no gate check
reads the embedded text. -/
def includedFiles : Array (Name × String) := #[
  (`NativeApp.Assets, "../../viewer/static/index.html"),
  (`NativeApp.Build, "../.lake/build/native-provenance.txt"),
  (`NativeApp.Build, "../.lake/build/native-source-inventory.txt"),
  (`NativeApp.Build, "../.lake/build/native-build-identity.txt")]

/-- Inspect parsed syntax rather than comment/literal-stripped source text.
Traversal is over the compiler-produced finite syntax tree. A node at any depth whose first
child is the atom `set_option` sets an option, as a command or before a term, a tactic sequence
or a grind sequence, and is held to `inspectOption`. -/
partial def inspectSyntax (owner : Name) (nodeSyntax : Syntax) : IO Unit := do
  let kind := nodeSyntax.getKind
  if kind == ``Parser.Command.docComment || kind == ``Parser.Command.moduleDoc ||
      kind == `str || kind == `char then return
  match nodeSyntax with
  | .atom _ word =>
    if forbiddenWords.contains word then reject owner s!"forbidden syntax capability {word}"
    -- An inclusion reaches this case only outside the admitted form below.
    if word.trimAscii.toString == "include_str" then
      reject owner "file inclusion outside its admitted form"
  | .ident _ _ name _ =>
    if name.components.any (fun part => part != `admit && forbiddenWords.contains part.toString) then
      reject owner s!"forbidden syntax identifier {name}"
  | .node _ kind children =>
    if let .atom _ word := nodeSyntax[0] then
      if word.trimAscii.toString == "set_option" then inspectOption owner nodeSyntax
    if kind == ``Parser.Term.attrInstance then
      unless nodeSyntax[1].isOfKind ``Parser.Attr.simple do
        reject owner s!"unreviewed attribute syntax {nodeSyntax[1].getKind}"
      let attributeName := nodeSyntax[1][0].getId
      unless allowedAttributes.contains attributeName do
        reject owner s!"unreviewed attribute {attributeName}"
      unless nodeSyntax[1][1].getArgs.isEmpty do
        reject owner s!"attribute arguments require review: {attributeName}"
    if kind == ``includeStr then
      let some path := nodeSyntax[1].isStrLit?
        | reject owner "file inclusion whose path is not a string literal"
      unless includedFiles.contains (owner, path) do
        reject owner s!"unreviewed file inclusion {path}"
      return
    for child in children do inspectSyntax owner child
  | .missing => reject owner "missing syntax node"

/-- Admit only ordinary declarations and scopes from the trusted command parser. -/
partial def inspectCommand (owner : Name) (command : Syntax) : IO Unit := do
  let kind := command.getKind
  if kind == ``Parser.Command.in then
    unless command.getArgs.size == 3 do reject owner "unexpected scoped-command shape"
    inspectCommand owner command[0]
    inspectCommand owner command[2]
  else if kind == ``Parser.Command.mutual then
    unless command.getArgs.size == 3 do reject owner "unexpected mutual-command shape"
    for declaration in command[1].getArgs do inspectCommand owner declaration
  else if proofOwner owner && kind == `Lean.guardMsgsCmd then
    let some nested := command.getArgs.back?
      | reject owner "empty message guard"
    unless #[``Parser.Command.printAxioms, ``Parser.Command.declaration].contains nested.getKind do
      reject owner "message guards may only inspect axioms or compiler-refusal declarations"
    inspectCommand owner nested
    inspectSyntax owner command
  else if proofOwner owner && kind == ``Parser.Command.printAxioms then
    inspectSyntax owner command
  else if #[``Parser.Command.declaration, ``Parser.Command.namespace, ``Parser.Command.end,
      ``Parser.Command.section, ``Parser.Command.open, ``Parser.Command.variable,
      ``Parser.Command.set_option, ``Parser.Command.moduleDoc, ``Parser.Command.eoi].contains kind then
    inspectSyntax owner command
  else reject owner s!"unreviewed command {kind}"

/-- Artifact ownership uses canonical paths, so namespace spelling and symlinks
cannot substitute another package for the pinned toolchain or current build. -/
def checkOrigin (root : System.FilePath) (name : Name) : IO Unit := do
  let root ← IO.FS.realPath root
  let expected := root / (name.toString.replace "." "/" ++ ".olean")
  let actual ← IO.FS.realPath (← findOLean name)
  unless actual == expected do reject name s!"artifact origin {actual}, expected {expected}"

/-- Parse one source without elaborating it or loading any project extension. -/
def inspectSource (parserEnv : Environment) (library : System.FilePath)
    (owners : Array Name) (owner : Name) : IO Unit := do
  let path : System.FilePath := owner.toString.replace "." "/" ++ ".lean"
  let source ← IO.FS.readFile path
  let context := Parser.mkInputContext source path.toString
  let (header, initial, initialMessages) ← Parser.parseHeader context
  if initialMessages.hasErrors then reject owner "header parse failed"
  for imported in Elab.headerToImports header do
    unless importAllowed owner imported.module do
      reject owner s!"unreviewed import {imported.module}"
    if !proofOwner owner && (`Std).isPrefixOf imported.module &&
        !(#[`Std.Data.TreeMap.Lemmas, `Std.Sync.Mutex].contains imported.module) &&
        !(owner == `Acorn.Host.Viewer.HttpServer && imported.module == `Std.Http.Server) &&
        !(owner == `Acorn.Host.Viewer.NativeContext &&
          imported.module == `Std.Time.DateTime.Timestamp) then
      reject owner s!"unreviewed direct standard import {imported.module}"
    if (`Init).isPrefixOf imported.module || (`Std).isPrefixOf imported.module then
      checkOrigin library imported.module
    if governed imported.module && !owners.contains imported.module then
      reject owner s!"import has no admitted regular source: {imported.module}"
  let mut state := initial
  let mut messages := initialMessages
  repeat
    let (command, next, log) := Parser.parseCommand context { env := parserEnv, options := {} } state messages
    if log.hasErrors then
      for message in log.toList do IO.eprintln (← message.toString)
      reject owner "source does not parse under the trusted parser"
    inspectCommand owner command
    if command.isOfKind ``Parser.Command.eoi then break
    unless state.pos < next.pos do reject owner "parser made no progress"
    state := next
    messages := log

/-- Source admission covers every discovered current module, including unimported files. -/
def sources (owners : Array Name) (proofs : Bool := false) : IO Unit := do
  let originalPath ← searchPathRef.get
  let library ← getLibDir (← findSysroot)
  -- Grammar owners are explicit: unsupported new syntax fails admission until
  -- its pinned parser owner is reviewed, without importing project sources.
  let parserModules := if proofs then #[`Mathlib.Tactic.FieldSimp,
    `Mathlib.Tactic.FinCases, `Mathlib.Tactic.Linarith, `Mathlib.Tactic.LinearCombination,
    `Mathlib.Tactic.NormNum, `Mathlib.Tactic.Positivity, `Mathlib.Tactic.Ring,
    `Mathlib.Tactic.SplitIfs, `Mathlib.Tactic.Convert, `Mathlib.Order.Filter.Defs,
    `Mathlib.Topology.Algebra.InfiniteSum.Defs, `Mathlib.Analysis.Normed.Group.Defs,
    `Aesop.Frontend.Tactic] else #[`Lean]
  if proofs then
    for parserModule in parserModules do
      let root := if (`Aesop).isPrefixOf parserModule then
          ".lake/packages/aesop/.lake/build/lib/lean"
        else ".lake/packages/mathlib/.lake/build/lib/lean"
      checkOrigin root parserModule
  else
    -- The runtime parser's entire closure resolves only in the sysroot.
    searchPathRef.set [library]
    checkOrigin library `Lean
  let parserEnv ← importModules (parserModules.map fun name => { module := name }) {}
    (leakEnv := true) (loadExts := true)
  searchPathRef.set originalPath
  let admitted ← AcornModuleInventory.projectModules
  for owner in owners do inspectSource parserEnv library admitted owner

/-- Compiler metadata must assign every imported declaration an actual owning module. -/
def declarationOwner (env : Environment) (name : Name) : IO Name := do
  let some index := env.getModuleIdxFor? name
    | throw (IO.userError s!"Lean boundary: declaration {name} has no owning module")
  let some imported := env.header.modules[index.toNat]?
    | throw (IO.userError s!"Lean boundary: declaration {name} has an invalid owning module")
  return imported.module

/-- Read the complete serialized import graph from a metadata-only environment.
Every artifact must resolve to an admitted source or canonical Init/Std module.
The graph remains inside the environment's lifetime; no second copy of the
compiled module regions is loaded or retained. -/
def artifactImports (env : Environment) (owners : Array Name)
    (library : System.FilePath) : IO (NameMap (Array Name)) := do
  unless env.header.modules.size == env.header.moduleData.size do
    reject Name.anonymous "module inventory and metadata differ"
  let mut imports : NameMap (Array Name) := {}
  for index in [:env.header.modules.size] do
    let name := env.header.modules[index]!.module
    if (`Init).isPrefixOf name || (`Std).isPrefixOf name then checkOrigin library name
    else if owners.contains name then checkOrigin ".lake/build/lib/lean" name
    else reject name "artifact import is outside admitted sources and the pinned Init/Std library"
    let some data := env.header.moduleData[index]?
      | reject name "missing module metadata"
    imports := imports.insert name (data.imports.map (·.module))
  return imports

/-- Traverse each owner's actual artifact imports, independently of shared environment loading. -/
def checkImports (imports : NameMap (Array Name)) (owner : Name) : IO Unit := do
  let mut pending := #[owner]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let some name := pending.back? | reject owner "lost import closure work item"
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    unless name == owner || importAllowed owner name do
      reject owner s!"transitive import crosses the boundary: {name}"
    let some dependencies := imports.find? name | reject owner s!"missing import metadata {name}"
    pending := pending ++ dependencies

/-- Dispatch each declaration to its compiler-recorded owner in one environment
traversal. Every selected owner receives the same declaration predicates: the capability
owner and the import layer of each constant a declaration references. -/
def inspectDeclarations (env : Environment) (owners : Array Name) : IO Unit := do
  let selected := owners.foldl (fun selected owner => selected.insert owner) ({} : NameSet)
  for (name, info) in env.constants do
    let owner ← declarationOwner env name
    if !selected.contains owner then continue
    for dependency in info.getUsedConstantsAsSet do
      unless capabilityAllowed owner dependency do
        reject owner s!"{name} uses unowned native capability {dependency}"
      let dependencyOwner ← declarationOwner env dependency
      unless dependencyOwner == owner || importAllowed owner dependencyOwner do
        reject owner s!"{name} references {dependency} owned by {dependencyOwner}"

/-- Check compiled declarations and their real referenced owners. The gate admits the
sources before the build, and `command` admits them again after this check.
The checks read declarations and module metadata alone, so no project extension
is initialized. Scoped imports release each environment after all its checks; only
names selected from the original source inventory escape the shared callback. -/
unsafe def compiled (owners : Array Name) : IO Unit := do
  let library ← getLibDir (← findSysroot)
  let inspect (env : Environment) (selected : Array Name) : IO Unit := do
    let imports ← artifactImports env owners library
    for owner in selected do
      unless (env.getModuleIdx? owner).isSome do
        reject owner "compiled module did not enter the environment"
      checkImports imports owner
    inspectDeclarations env selected
  -- Executable roots each own `main` and are loaded alone. Every other owner is loaded
  -- once, in one environment: a declaration's checks read only its owner's import closure.
  let shared := owners.filter fun owner => !AcornOwnership.executables.any (·.2 == owner)
  let included ← withImportModules (shared.map fun owner => { module := owner }) {} fun common => do
    let included := owners.filter fun owner => (common.getModuleIdx? owner).isSome
    inspect common included
    AcornDepartureAudit.check common owners
    pure included
  for owner in owners do
    if included.contains owner then continue
    withImportModules #[{ module := owner }] {} fun env => inspect env #[owner]

/-- The paths `.github/CODEOWNERS` names, read in a closed form. A line is empty, starts with
`#`, or is `/path @owner`: one space, a path of letters, digits, `.`, `_`, `-` and `/` after its
leading `/`, and an owner of letters, digits and `-` after its `@`. Any other line is refused, a
pattern with `*` included, and so is a file that names no path: this reader decides which modules
the owner holds, so it reads nothing it cannot read exactly. -/
def ownerPaths (file : System.FilePath := "../.github/CODEOWNERS") : IO (Array String) := do
  let word (allowed : Char → Bool) (text : String) : Bool :=
    !text.isEmpty && text.toList.all allowed
  let mut paths := #[]
  for line in (← IO.FS.readFile file).splitOn "\n" do
    if line.isEmpty || line.startsWith "#" then continue
    let [path, owner] := line.splitOn " "
      | reject Name.anonymous s!"{file}: a line that is not `/path @owner`: {line}"
    unless path.startsWith "/" && owner.startsWith "@" &&
        word (fun c => c.isAlphanum || "._-/".contains c) (path.drop 1).toString &&
        word (fun c => c.isAlphanum || c == '-') (owner.drop 1).toString do
      reject Name.anonymous s!"{file}: a line that is not `/path @owner`: {line}"
    paths := paths.push path
  if paths.isEmpty then reject Name.anonymous s!"{file} names no path"
  return paths

/-- Whether the source of a module of this package lies under one of the owner's paths: the
path is the module's file itself, or ends in `/` and the file lies below that directory. -/
def ownerCovered (paths : Array String) (module : Name) (package : String := "lean") : Bool :=
  let file := s!"/{package}/" ++ module.toString.replace "." "/" ++ ".lean"
  paths.any fun path => path == file || (path.endsWith "/" && file.startsWith path)

/-- The root document of the site and the library of its documents: the sources under
`site/AcornDocs` and `site/AcornDocs.lean`, which any change may edit and which
`site/Admit.lean` admits before they are elaborated. -/
def siteDocument (module : Name) : Bool := (`AcornDocs).isPrefixOf module

/-- The one module of the site's tooling that imports the documents: the renderer's root, which
applies the check to them. -/
def siteRenderer : Name := `Main

/-- The imports a source file declares, read with Lean's header parser. -/
def declaredImports (owner : Name) (path : System.FilePath) : IO (Array Name) := do
  let context := Parser.mkInputContext (← IO.FS.readFile path) path.toString
  let (header, _, messages) ← Parser.parseHeader context
  if messages.hasErrors then reject owner "header parse failed"
  return (Elab.headerToImports header).map (·.module)

/-- The tool module that pins the axioms of named theorems. It imports the modules whose theorems
it names, so it is the root of no executable and no other tool module imports it; its commands
print axioms and declare nothing. -/
def axiomPins : Name := `AcornTools.AxiomPins

/-- No gate tool, and no module of the documentation site's own tooling, imports a module from
outside the owner's paths. Starting from every tool module but the axiom pins, and from the
modules of this package that the site's tooling imports, each module's own import lines are read
with Lean's header parser and followed through the project's modules: every module reached lies
under a path that `.github/CODEOWNERS` names, and none is the axiom pins. The site's tooling is
itself under owner paths and imports no document, but for the renderer's root. A tool's own code is then elaborated with
no declaration of an unowned project module in scope, so no such declaration (an instance, a name
in a namespace the tool opens) can be what the tool's code resolves to, and a tool links no such
module. The modules of the toolchain and of the dependencies are not followed: the lock files,
which are owner paths, select them. -/
def toolImports : IO Unit := do
  let paths ← ownerPaths
  let project ← AcornModuleInventory.allModules
  if AcornOwnership.executables.any (·.2 == axiomPins) then
    reject axiomPins "the axiom pins are the root of an executable"
  unless ownerCovered paths axiomPins do reject axiomPins "tool module under no owner path"
  let mut pending := AcornModuleInventory.toolingModules.filter (· != axiomPins)
  -- The site's own tooling is every module of the site that is no document. It decides the
  -- site's check and holds the elaborators of the documents' references, so the same holds
  -- of it: under an owner path, and every module of this package it imports is followed with
  -- the gate tools' own. It imports no document; the renderer's root alone does, to apply the
  -- check to them.
  let mut tooling := 0
  for module in ← AcornModuleInventory.siteModules do
    if siteDocument module then continue
    tooling := tooling + 1
    unless ownerCovered paths module "site" do
      reject module "a module of the site's tooling under no owner path"
    let path := System.FilePath.mk ".." / "site" / (module.toString.replace "." "/" ++ ".lean")
    for imported in ← declaredImports module path do
      if project.contains imported then pending := pending.push imported
      if siteDocument imported && module != siteRenderer then
        reject module s!"the site's tooling imports the document {imported}"
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let some module := pending.back? | reject Name.anonymous "lost tool import work item"
    pending := pending.pop
    if seen.contains module then continue
    seen := seen.insert module
    if module == axiomPins then reject module "a gate tool imports the axiom pins"
    unless ownerCovered paths module do
      reject module
        "a gate tool or the site's tooling imports this module, which is under no owner path"
    for imported in ← declaredImports module (module.toString.replace "." "/" ++ ".lean") do
      if project.contains imported then pending := pending.push imported
  IO.println s!"lean-boundary-audit: {seen.size} modules of the gate's tools and {tooling} of the site's tooling, each under an owner path"

/-- Run source admission before build, or source plus compiled admission afterward.
Initializer execution is restricted to the trusted parser; compiled admission
reads project metadata without initializing project extensions. This tool is part of the reviewed verification trust boundary. -/
unsafe def command (args : List String) : IO UInt32 := do
  unless [["source"], ["compiled"], ["proof-source"]].contains args do
    IO.eprintln "usage: lean-boundary-audit (source|compiled|proof-source)"
    return 1
  Lean.initSearchPath (← Lean.findSysroot)
  let proofs := args == ["proof-source"]
  -- The decision registry states contracts, so it is admitted with the proof sources. Every
  -- other project module is admitted with the executing sources, whatever its library.
  let owners := (← AcornModuleInventory.projectModules).filter
    (if proofs then proofSide else fun name => !proofSide name)
  -- Before anything but this tool is built: no gate tool imports a module outside the owner's paths.
  if args == ["source"] then toolImports
  -- Compiled admission goes first. Source admission keeps its parser environment mapped
  -- until exit, and a module that is already mapped cannot be mapped again: it is read
  -- and relocated in full by every later environment that imports it.
  if args == ["compiled"] then AcornBoundaryAudit.compiled owners
  -- Every import turns initializer execution off again, so it is enabled for the parser alone.
  Lean.enableInitializersExecution
  AcornBoundaryAudit.sources owners proofs
  IO.println s!"lean-boundary-audit: {owners.size} modules admitted ({args.headD ""})"
  return 0

end AcornBoundaryAudit
