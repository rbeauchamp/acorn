/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.ModuleInventory
import AcornTools.Ownership

/-! # Compiler-linked ownership admission

Source discovery, Lake's evaluated executable configuration, and compiled
declaration ownership must agree. Required proof anchors name statements about
the actual executing definitions; their types must still refer to those owners.
This is coverage/routing admission, not an inference that names prove semantics.
Types, proof terms, the runtime boundary and review supply the semantic evidence.
-/
namespace AcornOwnershipAudit
open Lean

/-- AcornTools.Ownership refusals are fatal and identify the missing contract. -/
def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError s!"ownership: {message}")

/-- Every discovered source has a reviewed role, and stale entries are refused. -/
def sources : IO (Array Name) := do
  let actual ← AcornModuleInventory.allModules
  require (actual.toList.eraseDups.length == actual.size) "duplicate discovered module"
  require (AcornOwnership.modules.toList.eraseDups.length == AcornOwnership.modules.size)
    "duplicate registered module"
  for name in actual do
    require (AcornOwnership.modules.contains name) s!"unowned maintained module {name}"
  for name in AcornOwnership.modules do
    require (actual.contains name) s!"stale module owner {name}"
  return actual

/-- Read Lake's evaluated executable configuration through the offline bootstrap. -/
def targets : IO (Array (String × Name)) := do
  let output ← IO.Process.output {
    cmd := "lean", args := #["-DwarningAsError=true", "-DautoImplicit=false", "--run",
      "Bootstrap.lean", "script", "run", "acornTargets"] }
  require (output.exitCode == 0) s!"Lake target discovery failed: {output.stderr}"
  let values ← IO.ofExcept ((← IO.ofExcept (Json.parse output.stdout)).getArr?)
  let mut actual := #[]
  for value in values do
    let target ← IO.ofExcept (value.getObjValAs? String "target")
    let owner ← IO.ofExcept (value.getObjValAs? String "module")
    actual := actual.push (target, owner.toName)
  require (actual.toList.eraseDups.length == actual.size) "duplicate Lake executable"
  for entry in actual do
    require (AcornOwnership.executables.contains entry) s!"unowned Lake executable {entry}"
  for entry in AcornOwnership.executables do
    require (actual.contains entry) s!"stale executable owner {entry}"
  return actual

/-- Compiler module indices, rather than declaration namespaces, establish ownership. -/
def ownerOf (env : Environment) (name : Name) : IO Name := do
  let some index := env.getModuleIdxFor? name
    | throw (IO.userError s!"{name}: no compiled declaration owner")
  let some imported := env.header.modules[index.toNat]?
    | throw (IO.userError s!"{name}: invalid compiled owner index")
  return imported.module

/-- Follow actual compiler IR calls and closures, excluding erased proof/type references.
External compiler/library primitives end traversal and remain trusted. -/
def executionClosure (env : Environment) : IO NameSet := do
  let mut pending := #[`main]
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let some name := pending.back? | throw (IO.userError "lost IR work item")
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let owner ← ownerOf env name
    unless AcornOwnership.modules.contains owner do continue
    let some declaration := IR.findEnvDecl env name
      | throw (IO.userError s!"{owner}: missing compiler IR for {name}")
    require (!declaration.isExtern) s!"{owner}: external replacement for {name}"
    require declaration.getInfo.sorryDep?.isNone s!"{owner}: admitted hole in compiled {name}"
    pending := pending ++ IR.collectUsedDecls env [declaration]
  return seen

/-- Every declared entry must reach its own reviewed executing owners. -/
def entryContract (env : Environment) (owner : Name) : IO Unit := do
  let contracts := AcornOwnership.entryUses.filter (·.1 == owner)
  require (contracts.size == 1) s!"{owner}: missing or duplicate entry contract"
  let some (_, required) := contracts[0]? | throw (IO.userError "entry contract disappeared")
  require (!required.isEmpty) s!"{owner}: empty execution contract"
  let reachable ← executionClosure env
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

/-- All source modules are compiled, including modules not imported by a library root.
Non-entry modules share one compiler environment. Native entries remain isolated
because their `main` names overlap. AcornTools.Ownership, IR and initializer-name queries
read imported metadata directly; extension initialization is unnecessary.
Each isolated environment is freed after its complete entry check. -/
unsafe def compiled : IO Unit := do
  let modules ← sources
  let entries ← targets
  initSearchPath (← findSysroot)
  let shared := modules.filter fun owner =>
    owner != `Bootstrap && !entries.any (·.2 == owner)
  let common ← importModules (shared.map fun owner => { module := owner }) {}
    (leakEnv := true)
  for owner in modules do
    let path : System.FilePath := ".lake/build/lib/lean" / (owner.toString.replace "." "/" ++ ".olean")
    require ((← IO.FS.realPath (← findOLean owner)) == (← IO.FS.realPath path))
      s!"{owner}: compiled artifact resolves outside the current build"
    let isEntry := entries.any (·.2 == owner)
    let inspect (env : Environment) : IO Unit := do
      require ((env.getModuleIdx? owner).isSome) s!"{owner}: module absent from compiled environment"
      let ownsMain ← match env.find? `main with
        | some _ => do pure ((← ownerOf env `main) == owner)
        | none => pure false
      require (ownsMain == (isEntry || owner == `Bootstrap))
        s!"{owner}: compiled main and executable inventory disagree"
      if isEntry then entryContract env owner
      for (proofOwner, theoremName, implementation) in AcornOwnership.anchors do
        if proofOwner == owner then anchor env proofOwner theoremName implementation
    if isEntry then
      withImportModules #[{ module := owner, importAll := true, isMeta := true }] {} inspect
    else if (common.getModuleIdx? owner).isSome then inspect common
    else withImportModules #[{ module := owner }] {} inspect
  for (proofOwner, _, _) in AcornOwnership.anchors do
    require (modules.contains proofOwner) s!"stale proof owner {proofOwner}"
  for (owner, _) in AcornOwnership.entryUses do
    require (entries.any (·.2 == owner)) s!"stale entry contract {owner}"
  IO.println s!"ownership: {modules.size} maintained modules, {entries.size} native entries, {AcornOwnership.anchors.size} required execution/proof links"

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
    | _ => throw (IO.userError "usage: ownership-audit (source|compiled)")
    return 0
  catch error =>
    IO.eprintln s!"ownership-audit: {error}"
    return 1
