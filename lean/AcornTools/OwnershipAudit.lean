/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.OwnershipSource
import AcornTools.Theorems
import AcornTools.Corpus.Audit

/-! # Compiler-linked ownership admission

Source discovery, Lake's evaluated executable configuration, and compiled
declaration ownership must agree. The maintained modules are the discovered
sources. Required proof anchors name statements about the actual executing
definitions; their types must still refer to those owners.
This is coverage/routing admission, not an inference that names prove semantics.
Types, proof terms, the runtime boundary and review supply the semantic evidence.
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
External compiler/library primitives end traversal and remain trusted. `maintained` are the
discovered sources. -/
def executionClosure (env : Environment) (maintained : Array Name) (imports : NameSet) :
    IO NameSet := do
  let mut pending := #[`main]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let some name := pending.back? | throw (IO.userError "lost IR work item")
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let owner ← ownerOf env name
    require (imports.contains owner) s!"{name}: IR reference outside entry import closure: {owner}"
    unless maintained.contains owner do continue
    let some declaration := IR.findEnvDecl env name
      | throw (IO.userError s!"{owner}: missing compiler IR for {name}")
    require (!declaration.isExtern) s!"{owner}: external replacement for {name}"
    require declaration.getInfo.sorryDep?.isNone s!"{owner}: admitted hole in compiled {name}"
    pending := pending ++ IR.collectUsedDecls env [declaration]
  return seen

/-- Every declared entry must reach its own reviewed executing owners. -/
def entryContract (env : Environment) (maintained : Array Name) (owner : Name)
    (imports : NameSet) : IO Unit := do
  let contracts := AcornOwnership.entryUses.filter (·.1 == owner)
  require (contracts.size == 1) s!"{owner}: missing or duplicate entry contract"
  let some (_, required) := contracts[0]? | throw (IO.userError "entry contract disappeared")
  require (!required.isEmpty) s!"{owner}: empty execution contract"
  let reachable ← executionClosure env maintained imports
  let missing := required.filter (!reachable.contains ·)
  require missing.isEmpty s!"{owner}: native main no longer reaches {missing}"

/-- The required theorem's checked statement must still name its executable definition. -/
def anchor (env : Environment) (maintained : Array Name)
    (proofOwner theoremName implementation : Name) : IO Unit := do
  let some (.thmInfo theoremInfo) := env.find? theoremName
    | throw (IO.userError s!"missing required theorem {theoremName}")
  require ((← ownerOf env theoremName) == proofOwner) s!"{theoremName}: wrong proof owner"
  let some implementationInfo := env.find? implementation
    | throw (IO.userError s!"{theoremName}: missing execution owner {implementation}")
  require (!implementationInfo.isUnsafe && !implementationInfo.isPartial)
    s!"{implementation}: unreviewed execution replacement"
  require (maintained.contains (← ownerOf env implementation))
    s!"{implementation}: execution owner is not maintained"
  require (theoremInfo.type.getUsedConstantsAsSet.contains implementation)
    s!"{theoremName}: statement no longer refers to {implementation}"

/-- The decision kinds of `Regula.Contract`. A contract whose condition applies one of them to its
implementation (`appliesKind`) states which direction of the decision is proved. -/
def decisionKinds : Array Name :=
  #[`Regula.Decides, `Regula.DecidesSoundly, `Regula.DecidesCompletely]

/-- The modules that state decision contracts: the registry, and the proof module whose contracts
need the proof library. -/
def contractOwners : Array Name := #[AcornModuleInventory.decisionRegistry, `AcornVerif.Decisions]

/-- The binder kinds of a type, outermost first. -/
def binderInfos : Expr → List BinderInfo
  | .mdata _ type => binderInfos type
  | .forallE _ _ body binder => binder :: binderInfos body
  | _ => []

/-- Whether a contract's condition applies a decision kind `K` to the contract's implementation, in
one of two closed forms: `K accepts spec`, which lacks exactly the kind's last explicit argument, so
the contract applies it to the implementation; or `fun g => K accepts spec t`, whose last explicit
argument `t` contains the bound `g`, which the contract instantiates with the implementation. Every
other form is refused, such as `fun _ => K accepts spec id`, whose decision is not about the
implementation. -/
def appliesKind (env : Environment) (condition : Expr) : Bool := Id.run do
  let (body, bound) := match condition.consumeMData with
    | .lam _ _ body _ => (body.consumeMData, true)
    | condition => (condition, false)
  let .const kind _ := body.getAppFn | return false
  unless decisionKinds.contains kind do return false
  let some info := env.find? kind | return false
  let binders := binderInfos info.type
  unless binders.getLast?.any (·.isExplicit) do return false
  let args := body.getAppArgs
  if bound then
    return args.size == binders.length && args.back?.any (·.hasLooseBVar 0)
  else
    return args.size + 1 == binders.length

/-- Whether a type is that of a decision procedure: its result, after every binder, is a
`Decidable` proposition, which carries both directions of the decision in its type. -/
def decidableResult : Expr → Bool
  | .mdata _ type => decidableResult type
  | .forallE _ _ body _ => decidableResult body
  | type => #[`Decidable, `DecidableEq, `DecidablePred, `DecidableRel].contains
      type.getAppFn.constName

/-- The function a contract is about, when its subject is that function itself: a constant applied
to nothing but arguments its type takes implicitly (a universe-, type- or instance-level
instantiation). A subject applied to an explicit argument, such as `f x₀`, states the contract of
one application, and names no function here. -/
def wholeFunction (env : Environment) (subject : Expr) : Option Name := do
  let subject := subject.consumeMData
  let .const function _ := subject.getAppFn | none
  let mut type := (← env.find? function).type
  for _ in subject.getAppArgs do
    let .forallE _ _ body binder := type.consumeMData | none
    guard !binder.isExplicit
    type := body
  return function

/-- Every function the registry registers (`Regula.RegisteredDecision`) has a contract in
`contractOwners` about the whole function (`wholeFunction`) whose condition applies a decision kind
to that function (`appliesKind`), unless it is a decision procedure. Regula v0.13.0 reads no
registration or contract, so this audit is what makes a registration require its contract. A
registration outside the registry is refused, and so is a registry that registers nothing. Returns
the number of registrations. -/
def registrations (env : Environment) : IO Nat := do
  let mut registered : Array Name := #[]
  let mut contracted : NameSet := {}
  for (name, info) in env.constants do
    let .thmInfo theoremInfo := info | continue
    let type := theoremInfo.type.consumeMData
    let head := type.getAppFn
    let isRegistration := head.isConstOf `Regula.RegisteredDecision
    let isContract := head.isConstOf `Regula.ExecutableContract
    unless isRegistration || isContract do continue
    let owner ← ownerOf env name
    if isRegistration then
      require (owner == AcornModuleInventory.decisionRegistry)
        s!"{name}: a registration outside {AcornModuleInventory.decisionRegistry}"
      let some function := (type.getArgD 1 default).consumeMData.getAppFn.constName?
        | throw (IO.userError s!"{name}: registers no named function")
      registered := registered.push function
    else if contractOwners.contains owner && appliesKind env (type.getArgD 2 default) then
      if let some function := wholeFunction env (type.getArgD 1 default) then
        contracted := contracted.insert function
  require (!registered.isEmpty) "the decision registry registers no function"
  for function in registered do
    let some info := env.find? function
      | throw (IO.userError s!"{function}: registered, and absent from the environment")
    unless decidableResult info.type || contracted.contains function do
      throw (IO.userError
        s!"{function}: registered with no contract that applies a decision kind to it")
  return registered.size

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
released, while the common environment also serves the theorem inventory and
document admission.
Complete mode initializes the same reviewed non-entry scope used by corpus
admission, after source admission; standalone ownership needs no extensions. -/
unsafe def compiled (complete : Bool := false) : IO Unit := do
  let modules ← sources
  let entries ← targets modules
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
          entryContract env modules owner (← importClosure env owner)
        for (proofOwner, theoremName, implementation) in AcornOwnership.anchors do
          if proofOwner == owner then anchor env modules proofOwner theoremName implementation
      if isEntry then
        let imports := #[{ module := owner, importAll := true, isMeta := true : Import }]
        let (_, state) ← (importModulesCore imports).run base
        let env ← finalizeImport state imports {} (leakEnv := false) (loadExts := false)
        inspect env
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
    let registered ← registrations common
    IO.println (s!"ownership: {modules.size} maintained modules, {entries.size} native entries, " ++
      s!"{AcornOwnership.anchors.size} required execution/proof links, " ++
      s!"{registered} registered decisions")
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
      discard (AcornOwnershipAudit.targets (← AcornOwnershipAudit.sources))
      IO.println "ownership: source modules and Lake entries admitted"
    | ["compiled"] => AcornOwnershipAudit.compiled
    | ["complete"] => AcornOwnershipAudit.compiled true
    | _ => throw (IO.userError "usage: ownership-audit (source|compiled|complete)")
    return 0
  catch error =>
    IO.eprintln s!"ownership-audit: {error}"
    return 1
