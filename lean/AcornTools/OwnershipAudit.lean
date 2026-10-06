/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.OwnershipSource
import AcornTools.Theorems
import AcornTools.Corpus.Audit
import Acorn.Host.AgentAdmission

/-! # Compiler-linked ownership admission

Source discovery, Lake's evaluated executable configuration, and compiled
declaration ownership must agree. Required proof anchors name statements about
the actual executing definitions; their types must still refer to those owners.
This is coverage/routing admission, not an inference that names prove semantics.
Types, proof terms, the runtime boundary and review supply the semantic evidence.

## Sealed constants

A private constructor stops the constructor notation outside its module. It does not stop
a tactic: `by constructor` applies it anywhere. So the audit reads the compiled
declarations. For every private constructor of a type of a maintained project module, and
for every row of `AcornOwnership.sealedConstants`, no declaration of a project module
outside the permitted modules, other than a theorem, references the constant. A value of
a structure type is an application of its constructor, so a definition that makes a
value references the constructor or calls a declaration that does; a term written through
structure eta or a tactic contains the constructor after elaboration, which is what this
rule reads.

A theorem is exempt: compiled code gets no value from a proof, and the equations that
Lean derives for a definition are theorems of the module that first uses them. A
`noncomputable` definition could take a sealed value out of a proof by choice; it is not
executed. The rule is about this project's modules. It does not stop a definition in
another project, and it says nothing about bytes in a file.

`sealedControl` and `tableControl` below make a sealed value outside its module. The
audit runs the same rule on this module and requires exactly these two reports, so a rule
that reports nothing fails.
-/
namespace AcornOwnershipAudit
open Lean

/-- Compiler module indices, rather than declaration namespaces, establish ownership. -/
def ownerOf (env : Environment) (name : Name) : IO Name := do
  let some index := env.getModuleIdxFor? name
    | throw (IO.userError s!"{name}: no compiled declaration owner")
  let some imported := env.header.modules[index.toNat]?
    | throw (IO.userError s!"{name}: invalid compiled owner index")
  return imported.module

/-- Follow actual compiler IR calls and closures, excluding erased proof/type references.
External compiler/library primitives end traversal and remain trusted. -/
def executionClosure (env : Environment) (imports : NameSet) : IO NameSet := do
  let mut pending := #[`main]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let some name := pending.back? | throw (IO.userError "lost IR work item")
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let owner ← ownerOf env name
    require (imports.contains owner) s!"{name}: IR reference outside entry import closure: {owner}"
    unless AcornOwnership.modules.contains owner do continue
    let some declaration := IR.findEnvDecl env name
      | throw (IO.userError s!"{owner}: missing compiler IR for {name}")
    require (!declaration.isExtern) s!"{owner}: external replacement for {name}"
    require declaration.getInfo.sorryDep?.isNone s!"{owner}: admitted hole in compiled {name}"
    pending := pending ++ IR.collectUsedDecls env [declaration]
  return seen

/-- Every declared entry must reach its own reviewed executing owners. -/
def entryContract (env : Environment) (owner : Name) (imports : NameSet) : IO Unit := do
  let contracts := AcornOwnership.entryUses.filter (·.1 == owner)
  require (contracts.size == 1) s!"{owner}: missing or duplicate entry contract"
  let some (_, required) := contracts[0]? | throw (IO.userError "entry contract disappeared")
  require (!required.isEmpty) s!"{owner}: empty execution contract"
  let reachable ← executionClosure env imports
  let missing := required.filter (!reachable.contains ·)
  require missing.isEmpty s!"{owner}: native main no longer reaches {missing}"

/-- The required theorem's checked statement must still name its executable definition. -/
def anchor (env : Environment) (proofOwner theoremName implementation : Name) : IO Unit := do
  let some (.thmInfo theoremInfo) := env.find? theoremName
    | throw (IO.userError s!"missing required theorem {theoremName}")
  require ((← ownerOf env theoremName) == proofOwner) s!"{theoremName}: wrong proof owner"
  let some implementationInfo := env.find? implementation
    | throw (IO.userError s!"{theoremName}: missing execution owner {implementation}")
  require (!implementationInfo.isUnsafe && !implementationInfo.isPartial)
    s!"{implementation}: unreviewed execution replacement"
  require (AcornOwnership.modules.contains (← ownerOf env implementation))
    s!"{implementation}: execution owner is not maintained"
  require (theoremInfo.type.getUsedConstantsAsSet.contains implementation)
    s!"{theoremName}: statement no longer refers to {implementation}"

/-- Control of the sealed-constant rule for a private constructor: a state of a
construction from a learner state of no declared history, made outside the module of the
type with the `constructor` tactic. Nothing calls it; the audit requires that the rule
reports it. -/
def sealedControl (construction : Acorn.Handcrafted.AgentConstruction)
    (agent : Acorn.Handcrafted.Agent Acorn.Handcrafted.Grid.interface construction.profile
      construction.config construction.criterion construction.dimension construction.planning) :
    construction.State := by
  constructor
  exact agent

/-- Control of the sealed-constant rule for a table row: the callback record of one step
order copied under the index of the other. Nothing calls it; the audit requires that the
rule reports it. -/
def tableControl {α β : Type} (callbacks : Acorn.Host.AgentCallbacks .planAfterAct α β) :
    Acorn.Host.AgentCallbacks .learnThenAct α β :=
  { Chosen := callbacks.Chosen, choose := callbacks.choose, learn := callbacks.learn,
    recordEnvironment := callbacks.recordEnvironment, recordAttempt := callbacks.recordAttempt,
    capture := callbacks.capture, metrics := callbacks.metrics }

/-- The sealed constants of one compiled environment with the modules that may reference
each: every private constructor of a type that a project module declares, with that
module, and each row of `AcornOwnership.sealedConstants` that the environment holds. -/
def sealedIn (env : Environment) (projects : Array Name) : IO (NameMap (Array Name)) := do
  let mut permitted : NameMap (Array Name) := {}
  for (name, info) in env.constants do
    if let .ctorInfo constructor := info then
      if isPrivateName name then
        let owner ← ownerOf env constructor.induct
        if projects.contains owner then permitted := permitted.insert name #[owner]
  for (name, owners) in AcornOwnership.sealedConstants do
    if (env.find? name).isSome then permitted := permitted.insert name owners
  return permitted

/-- Each declaration of the selected modules, other than a theorem, that references a
sealed constant outside its permitted modules: the owner, the declaration, the constant. -/
def sealedViolations (env : Environment) (permitted : NameMap (Array Name))
    (selected : Array Name) : IO (Array (Name × Name × Name)) := do
  let mut found := #[]
  for (name, info) in env.constants do
    if let .thmInfo _ := info then continue
    let some index := env.getModuleIdxFor? name | continue
    let some imported := env.header.modules[index.toNat]?
      | throw (IO.userError s!"{name}: invalid compiled owner index")
    let owner := imported.module
    unless selected.contains owner do continue
    for used in info.getUsedConstantsAsSet do
      if let some owners := permitted.find? used then
        unless owners.contains owner do found := found.push (owner, name, used)
  return found

/-- No selected project module makes a sealed value outside the permitted modules. -/
def sealedAdmission (env : Environment) (projects selected : Array Name) : IO Unit := do
  let permitted ← sealedIn env projects
  for (owner, name, used) in ← sealedViolations env permitted selected do
    throw (IO.userError s!"{owner}: {name} references the sealed constant {privateToUserName used}; only {permitted.find? used |>.getD #[]} may")

/-- Each type of `AcornOwnership.sealedTypes` exists and each of its constructors is
sealed, and each table row names a compiled constant and maintained modules. -/
def sealedRequired (env : Environment) (projects modules : Array Name) : IO Unit := do
  let permitted ← sealedIn env projects
  for type in AcornOwnership.sealedTypes do
    let some (.inductInfo info) := env.find? type
      | throw (IO.userError s!"missing sealed type {type}")
    for constructor in info.ctors do
      require (permitted.contains constructor)
        s!"{type}: the constructor {constructor} is neither private nor a sealed table row"
  for (name, owners) in AcornOwnership.sealedConstants do
    require ((env.find? name).isSome) s!"stale sealed constant {name}"
    for owner in owners do
      require (modules.contains owner) s!"{name}: stale permitted module {owner}"
    require (owners.contains (← ownerOf env name)) s!"{name}: its own module is not permitted"

/-- The rule must report the two controls of this module, and nothing else in it. -/
def sealedControls (env : Environment) (projects : Array Name) : IO Unit := do
  let permitted ← sealedIn env projects
  let found := (← sealedViolations env permitted #[`AcornTools.OwnershipAudit]).map (·.2.1)
  require (found.contains ``sealedControl) "the sealed-constant rule did not report its control of a private constructor"
  require (found.contains ``tableControl) "the sealed-constant rule did not report its control of a table row"
  require (found.all fun name => name == ``sealedControl || name == ``tableControl)
    s!"the audit module makes a sealed value outside its controls: {found}"

/-- Follow the entry's actual serialized import edges. Shared dependency data
must never make a declaration outside this closure available to its IR check. -/
def importClosure (env : Environment) (root : Name) : IO NameSet := do
  let mut seen : NameSet := {}
  let mut pending := #[root]
  while !pending.isEmpty do
    let some owner := pending.back? | throw (IO.userError "lost import work item")
    pending := pending.pop
    if seen.contains owner then continue
    seen := seen.insert owner
    let some index := env.getModuleIdx? owner
      | throw (IO.userError s!"{owner}: missing compiled import owner")
    let some data := env.header.moduleData[index.toNat]?
      | throw (IO.userError s!"{owner}: missing compiled import data")
    pending := pending ++ data.imports.map (·.module)
  return seen

/-- Reuse compiler-loaded dependency regions, keeping each executable's `main`
isolated. Lean itself constructs every environment and rejects conflicting
constants. Regions remain alive until this bounded audit process exits;
no sibling environment may free shared regions. Ordinary sibling maps are
released, while the common environment also serves axiom/document admission.
Complete mode initializes the same reviewed non-entry scope used by corpus
admission, after source admission; standalone ownership needs no extensions. -/
unsafe def compiled (complete : Bool := false) : IO Unit := do
  let modules ← sources
  let entries ← targets
  initSearchPath (← findSysroot)
  for owner in modules do
    let path : System.FilePath := ".lake/build/lib/lean" / (owner.toString.replace "." "/" ++ ".olean")
    require ((← IO.FS.realPath (← findOLean owner)) == (← IO.FS.realPath path))
      s!"{owner}: compiled artifact resolves outside the current build"
  let mut dependencies : Array Import := #[]
  for (_, owner) in entries do
    let (data, _) ← readModuleData (← findOLean owner)
    dependencies := dependencies ++ data.imports.map fun imp =>
      { imp with importAll := true, isMeta := true }
  withImporting do
    let (_, base) ← (importModulesCore dependencies).run
    let shared := modules.filter fun owner => !entries.any (·.2 == owner)
    let commonImports := shared.map fun owner => { module := owner : Import }
    let (_, commonState) ← (importModulesCore commonImports).run base
    if complete then enableInitializersExecution
    let common ← finalizeImport commonState commonImports {} (leakEnv := true) (loadExts := complete)
    let projects := modules.filter (!AcornModuleInventory.toolingModules.contains ·)
    let included := projects.filter fun owner => (common.getModuleIdx? owner).isSome
    sealedRequired common projects modules
    sealedAdmission common projects included
    let mut counts : AcornTheoremCount.Counts := {}
    if complete then counts ← AcornTheoremCount.countEnvironment common included
    let mut counted := included
    for owner in modules do
      let isEntry := entries.any (·.2 == owner)
      let inspect (env : Environment) : IO Unit := do
        require ((env.getModuleIdx? owner).isSome) s!"{owner}: module absent from compiled environment"
        let ownsMain ← match env.find? `main with
          | some _ => do pure ((← ownerOf env `main) == owner)
          | none => pure false
        require (ownsMain == (isEntry || owner == `Bootstrap))
          s!"{owner}: compiled main and executable inventory disagree"
        if isEntry then
          require ((getModuleDoc? env owner).any (·.any (·.doc.any (!·.isWhitespace : Char → Bool))))
            s!"{owner}: executable root lacks a module docstring"
          entryContract env owner (← importClosure env owner)
        for (proofOwner, theoremName, implementation) in AcornOwnership.anchors do
          if proofOwner == owner then anchor env proofOwner theoremName implementation
      if isEntry then
        let imports := #[{ module := owner, importAll := true, isMeta := true : Import }]
        let (_, state) ← (importModulesCore imports).run base
        let env ← finalizeImport state imports {} (leakEnv := false) (loadExts := false)
        inspect env
        if projects.contains owner then sealedAdmission env projects #[owner]
        if owner == `AcornTools.OwnershipAudit then sealedControls env projects
        if complete && projects.contains owner && !counted.contains owner then
          let extra ← AcornTheoremCount.countEnvironment env #[owner]
          counts := counts.add extra
          counted := counted.push owner
      else
        inspect common
    for (proofOwner, _, _) in AcornOwnership.anchors do
      require (modules.contains proofOwner) s!"stale proof owner {proofOwner}"
    for (owner, _) in AcornOwnership.entryUses do
      require (entries.any (·.2 == owner)) s!"stale entry contract {owner}"
    IO.println s!"ownership: {modules.size} maintained modules, {entries.size} native entries, {AcornOwnership.anchors.size} required execution/proof links"
    IO.println s!"ownership: {(← sealedIn common projects).size} sealed constants have no reference in a definition outside their modules; 2 controls reported"
    if complete then
      require (projects.all counted.contains && counted.size == projects.size)
        "incomplete or duplicate theorem-owner admission"
      counts.report
      let cwd ← IO.Process.getCurrentDir
      try
        IO.Process.setCurrentDir ".."
        AcornCorpus.check (env? := some common)
      finally IO.Process.setCurrentDir cwd

end AcornOwnershipAudit

/-- Source/target admission can run before project modules are compiled. -/
unsafe def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["source"] =>
      discard AcornOwnershipAudit.sources
      discard AcornOwnershipAudit.targets
      IO.println "ownership: source modules and Lake entries admitted"
    | ["compiled"] => AcornOwnershipAudit.compiled
    | ["complete"] => AcornOwnershipAudit.compiled true
    | _ => throw (IO.userError "usage: ownership-audit (source|compiled|complete)")
    return 0
  catch error =>
    IO.eprintln s!"ownership-audit: {error}"
    return 1
