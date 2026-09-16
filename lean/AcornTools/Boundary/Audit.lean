/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.ModuleInventory
import AcornTools.Boundary.Departures

/-!
# Admission of the current Lean execution boundary

Source is parsed with the pinned compiler's trusted parser environment before
project extensions are loaded. Current modules cannot define parser/elaborator
extensions or native replacements. Compiled metadata then checks actual module
ownership, including private/generated declarations and transitive imports.

This verification tool and the pinned Lean/Init toolchain are trusted. The gate
does not prove compiler correctness or the truth of a provenance declaration.
-/
namespace AcornBoundaryAudit
open Lean

/-- Explicit composition roots may join learned and declared code. -/
def compositionRoots : Array Name := #[`Acorn, `Acorn.SwiftTdDriver, `Acorn.FeatureDriver, `Acorn.WorldDriver, `Acorn.ControlDriver, `Acorn.TemporalDriver, `Acorn.AgentDriver]

/-- Executing application sources and their shared constant leaf. -/
def governed (name : Name) : Bool := (`Acorn).isPrefixOf name ||
  (`NativeApp).isPrefixOf name

/-- Mathematical proofs have separate import admission. -/
def proofOwner (name : Name) : Bool := (`AcornVerif).isPrefixOf name

/-- Native entry/resource owners are checked as host code, never learned algorithms. -/
def nativeBootstrap (name : Name) : Bool := (`NativeApp).isPrefixOf name

/-- Host and declared modules are quarantined by their owning module, not namespaces. -/
def quarantined (name : Name) : Bool :=
  (`Acorn.Host).isPrefixOf name || (`Acorn.Handcrafted).isPrefixOf name

/-- Every other current module is learned, including any newly added nested module. -/
def learned (name : Name) : Bool :=
  (`Acorn).isPrefixOf name && !quarantined name && !compositionRoots.contains name

/-- Only host/composition owners may use the pinned standard containers and IO support.
Proof imports name their actual dependencies; Mathlib umbrella imports needlessly
load the entire library or tactic collection into each compiler process. -/
def importAllowed (owner imported : Name) : Bool :=
  if (`Init).isPrefixOf imported then true
  else if proofOwner owner then
    !#[`Mathlib, `Mathlib.Tactic].contains imported &&
      #[`Acorn, `AcornVerif, `Mathlib, `Lean, `Std].any (·.isPrefixOf imported)
  else if nativeBootstrap owner then
    (`NativeApp).isPrefixOf imported || (`Acorn).isPrefixOf imported || (`Std).isPrefixOf imported
  else if owner == `Acorn.Constants then false
  else if (`Std).isPrefixOf imported then
    (`Acorn.Host).isPrefixOf owner || compositionRoots.contains owner
  else if !(`Acorn).isPrefixOf imported then false
  else if learned owner then learned imported else true

/-- Errors include both the source owner and rejected capability. -/
def reject {α : Type} (owner : Name) (reason : String) : IO α :=
  throw (IO.userError s!"Lean boundary {owner}: {reason}")

/-- A small reviewed attribute domain has no native replacement or metaprogram registration. -/
def allowedAttributes : Array Name := #[`simp, `inline, `noinline, `reducible, `irreducible]

/-- These options change proof resource limits, never kernel checking or parser admission. -/
def allowedOptions : Array Name := #[`maxRecDepth, `maxHeartbeats, `exponentiation.threshold]

/-- Only these admitted host boundaries may create or inspect native subprocesses. -/
def processOwners : Array Name := #[`Acorn.Host.Checkpoint.IO, `Acorn.Host.Control,
  `Acorn.Host.Viewer.RunDirectory, `Acorn.Host.Viewer.ProcessOwner,
  `Acorn.Host.Viewer.NativeResources, `NativeApp.Viewer]

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

/-- Inspect parsed syntax rather than comment/literal-stripped source text.
Traversal is over the compiler-produced finite syntax tree. -/
partial def inspectSyntax (owner : Name) (nodeSyntax : Syntax) : IO Unit := do
  let kind := nodeSyntax.getKind
  if kind == ``Parser.Command.docComment || kind == ``Parser.Command.moduleDoc ||
      kind == `str || kind == `char then return
  match nodeSyntax with
  | .atom _ word =>
    if forbiddenWords.contains word then reject owner s!"forbidden syntax capability {word}"
  | .ident _ _ name _ =>
    if name.components.any (fun part => part != `admit && forbiddenWords.contains part.toString) then
      reject owner s!"forbidden syntax identifier {name}"
  | .node _ kind children =>
    if kind == ``Parser.Term.attrInstance then
      unless nodeSyntax[1].isOfKind ``Parser.Attr.simple do
        reject owner s!"unreviewed attribute syntax {nodeSyntax[1].getKind}"
      let attributeName := nodeSyntax[1][0].getId
      unless allowedAttributes.contains attributeName do
        reject owner s!"unreviewed attribute {attributeName}"
      unless nodeSyntax[1][1].getArgs.isEmpty do
        reject owner s!"attribute arguments require review: {attributeName}"
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
  else if kind == ``Parser.Command.set_option then
    let option := command[1].getId
    unless allowedOptions.contains option || (proofOwner owner && option == `linter.hashCommand) do
      reject owner s!"unreviewed option {option}"
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
      ``Parser.Command.moduleDoc, ``Parser.Command.eoi].contains kind then
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

/-- Native reflection and admitted proof holes cannot hide behind a generated name. -/
def forbiddenConstant (name : Name) : Bool :=
  name == `sorryAx || name == `Lean.ofReduceBool || name == `Lean.ofReduceNat ||
    name == `Lean.trustCompiler

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
traversal. Every selected owner receives the same declaration predicates. -/
def inspectDeclarations (env : Environment) (owners : Array Name) : IO Unit := do
  let selected := owners.foldl (fun selected owner => selected.insert owner) ({} : NameSet)
  for (name, info) in env.constants do
    let owner ← declarationOwner env name
    if !selected.contains owner then continue
    if let .axiomInfo _ := info then reject owner s!"project axiom {name}"
    if info.isUnsafe || info.isPartial then
      -- The pinned elaborator creates partial execution companions for safe
      -- structural recursion. Source admission forbids spelling this suffix.
      let some parent := Compiler.isUnsafeRecName? name
        | reject owner s!"unsafe or partial declaration {name}"
      let some parentInfo := env.find? parent
        | reject owner s!"orphan recursive companion {name}"
      unless info.isPartial && !parentInfo.isUnsafe && !parentInfo.isPartial &&
          (← declarationOwner env parent) == owner do
        reject owner s!"unreviewed recursive companion {name}"
    if (Compiler.getImplementedBy? env name).isSome || (getExternAttrData? env name).isSome then
      reject owner s!"custom native implementation for {name}"
    for dependency in info.getUsedConstantsAsSet do
      if forbiddenConstant dependency then reject owner s!"{name} uses {dependency}"
      unless capabilityAllowed owner dependency do
        reject owner s!"{name} uses unowned native capability {dependency}"
      let dependencyOwner ← declarationOwner env dependency
      unless dependencyOwner == owner || importAllowed owner dependencyOwner do
        reject owner s!"{name} references {dependency} owned by {dependencyOwner}"

/-- Check compiled declarations and their real referenced owners after source admission.
Pinned Lean's parametric attribute queries read imported module entries directly
once declaration ownership is established. No project extension initialization
is needed. Scoped imports release each environment after all its checks; only
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
  let included ← withImportModules #[{ module := `Acorn },
      { module := `NativeApp }] {} fun common => do
    let included := owners.filter fun owner => (common.getModuleIdx? owner).isSome
    inspect common included
    AcornDepartureAudit.check common
    pure included
  for owner in owners do
    if included.contains owner then continue
    withImportModules #[{ module := owner }] {} fun env => inspect env #[owner]

/-- Run source admission before build, or source plus compiled admission afterward.
Initializer execution is restricted to the trusted parser; compiled admission
reads project metadata without initializing project extensions. This tool is part of the reviewed verification trust boundary. -/
unsafe def command (args : List String) : IO UInt32 := do
  unless [["source"], ["compiled"], ["proof-source"]].contains args do
    IO.eprintln "usage: lean-boundary-audit (source|compiled|proof-source)"
    return 1
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.enableInitializersExecution
  let proofs := args == ["proof-source"]
  let owners := (← AcornModuleInventory.projectModules).filter
    (if proofs then proofOwner else governed)
  AcornBoundaryAudit.sources owners proofs
  if args == ["compiled"] then AcornBoundaryAudit.compiled owners
  IO.println s!"lean-boundary-audit: {owners.size} modules admitted ({args.headD ""})"
  return 0

end AcornBoundaryAudit
