import AcornTools.ModuleInventory
import AcornTools.Ownership
import AcornTools.Boundary.Departures
import AcornTools.TrackedFiles

namespace AcornBoundaryAudit
open Lean

def compositionRoots : Array Name := #[`Acorn, `Acorn.SwiftTdDriver, `Acorn.FeatureDriver, `Acorn.WorldDriver, `Acorn.ControlDriver, `Acorn.TemporalDriver, `Acorn.AgentDriver]

def registry (name : Name) : Bool := name == AcornModuleInventory.decisionRegistry

def entry (name : Name) : Bool := (`Entry).isPrefixOf name

def governed (name : Name) : Bool := ((`Acorn).isPrefixOf name ||
  (`NativeApp).isPrefixOf name || entry name) && !registry name

def proofOwner (name : Name) : Bool := (`AcornVerif).isPrefixOf name

def nativeBootstrap (name : Name) : Bool := (`NativeApp).isPrefixOf name || entry name

def quarantined (name : Name) : Bool :=
  (`Acorn.Host).isPrefixOf name || (`Acorn.Handcrafted).isPrefixOf name

def learned (name : Name) : Bool :=
  (`Acorn).isPrefixOf name && !quarantined name && !compositionRoots.contains name

def gridOwners : Array Name := #[`Acorn.Handcrafted.Observation, `Acorn.Handcrafted.Cumulants,
  `Acorn.Handcrafted.GridWorld]

def microduckOwners : Array Name := #[`Acorn.Handcrafted.Microduck]

def worldOwners : Array Name := gridOwners ++ microduckOwners

def worldIndependent (name : Name) : Bool :=
  (`Acorn.Handcrafted).isPrefixOf name && !worldOwners.contains name

def proofContracts : Name := `AcornVerif.Decisions

def floatLibBridge : Name := `AcornVerif.FloatLibBridge

def leanIntentBridge : Name := `AcornVerif.LeanIntentBridge

def generatorOnly (name : Name) : Bool :=
  #[`Acorn.Host.Certificate, `Acorn.Host.CertificateSearch, `Acorn.Host.CertificateDriver].contains name

def generatorExcluded (imported : Name) : Bool :=
  (`Acorn.Handcrafted).isPrefixOf imported ||
    #[`Acorn.Host.Runner, `Acorn.Host.Baseline].contains imported

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
  else if owner == `Acorn.Constants then false
  else if (`Std).isPrefixOf imported then
    (`Acorn.Host).isPrefixOf owner || compositionRoots.contains owner
  else if !(`Acorn).isPrefixOf imported then false
  else if learned owner then learned imported
  else if worldIndependent owner then learned imported || worldIndependent imported
  else true

def reject {α : Type} (owner : Name) (reason : String) : IO α :=
  throw (IO.userError s!"Lean boundary {owner}: {reason}")

def allowedAttributes : Array Name := #[`simp, `inline, `noinline, `reducible, `irreducible]

def allowedOptions : Array Name := #[`maxRecDepth, `maxHeartbeats, `exponentiation.threshold]

def processOwners : Array Name := #[`Acorn.Host.Checkpoint.IO, `Acorn.Host.Control,
  `Acorn.Host.Viewer.RunDirectory, `Acorn.Host.Viewer.ProcessOwner,
  `Acorn.Host.Viewer.NativeResources, `Acorn.Host.Microduck.Transport, `NativeApp.Viewer]

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

def forbiddenWords : Array String := #["unsafe", "partial", "meta", "axiom", "sorry", "admit",
  "native_decide", "run_tac", "run_elab", "by_elab", "extern", "implemented_by", "csimp",
  "simproc", "builtin_simproc", "elab", "macro", "initialize", "builtin_initialize", "_unsafe_rec"]

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

def checkOrigin (root : System.FilePath) (name : Name) : IO Unit := do
  let root ← IO.FS.realPath root
  let expected := root / (name.toString.replace "." "/" ++ ".olean")
  let actual ← IO.FS.realPath (← findOLean name)
  unless actual == expected do reject name s!"artifact origin {actual}, expected {expected}"

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

def sources (owners : Array Name) (proofs : Bool := false) : IO Unit := do
  let originalPath ← searchPathRef.get
  let library ← getLibDir (← findSysroot)
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
    searchPathRef.set [library]
    checkOrigin library `Lean
  let parserEnv ← importModules (parserModules.map fun name => { module := name }) {}
    (leakEnv := true) (loadExts := true)
  searchPathRef.set originalPath
  let admitted ← AcornModuleInventory.projectModules
  for owner in owners do inspectSource parserEnv library admitted owner

def declarationOwner (env : Environment) (name : Name) : IO Name := do
  let some index := env.getModuleIdxFor? name
    | throw (IO.userError s!"Lean boundary: declaration {name} has no owning module")
  let some imported := env.header.modules[index.toNat]?
    | throw (IO.userError s!"Lean boundary: declaration {name} has an invalid owning module")
  return imported.module

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

def flushOLeanCache (library : System.FilePath) : IO Unit := do
  let original ← searchPathRef.get
  try
    searchPathRef.set [library]
    let _ ← findOLean `Init
    searchPathRef.set [library, library]
    let _ ← findOLean `Init
  finally
    searchPathRef.set original

unsafe def withScopedImportModules {α : Type} (library : System.FilePath)
    (imports : Array Import) (opts : Options) (action : Environment → IO α) : IO α :=
  withImportModules imports opts fun env => do
    try
      action env
    finally
      flushOLeanCache library

unsafe def compiled (owners : Array Name) : IO Unit := do
  let library ← getLibDir (← findSysroot)
  let inspect (env : Environment) (selected : Array Name) : IO Unit := do
    let imports ← artifactImports env owners library
    for owner in selected do
      unless (env.getModuleIdx? owner).isSome do
        reject owner "compiled module did not enter the environment"
      checkImports imports owner
    inspectDeclarations env selected
  let shared := owners.filter fun owner => !AcornOwnership.executables.any (·.2 == owner)
  let included ← withScopedImportModules library (shared.map fun owner => { module := owner }) {}
    fun common => do
      let included := owners.filter fun owner => (common.getModuleIdx? owner).isSome
      inspect common included
      AcornDepartureAudit.check common owners
      pure included
  for owner in owners do
    if included.contains owner then continue
    withScopedImportModules library #[{ module := owner }] {} fun env =>
      inspect env #[owner]

unsafe def command (args : List String) : IO UInt32 := do
  unless [["source"], ["compiled"], ["proof-source"]].contains args do
    IO.eprintln "usage: lean-boundary-audit (source|compiled|proof-source)"
    return 1
  AcornTrackedFiles.admitLeanToolchain
  Lean.initSearchPath (← Lean.findSysroot)
  let proofs := args == ["proof-source"]
  let owners := (← AcornModuleInventory.projectModules).filter
    (if proofs then fun name => proofOwner name || registry name else governed)
  if args == ["compiled"] then AcornBoundaryAudit.compiled owners
  Lean.enableInitializersExecution
  AcornBoundaryAudit.sources owners proofs
  IO.println s!"lean-boundary-audit: {owners.size} modules admitted ({args.headD ""})"
  return 0

end AcornBoundaryAudit
