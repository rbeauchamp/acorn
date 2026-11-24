import AcornTools.Boundary.Audit
import AcornTools.Ownership
import AcornTools.TrackedFiles
import Regula.Load

namespace AcornTheoremCount

open Lean

structure Counts where
  verification : Nat := 0
  current : Nat := 0
  application : Nat := 0
  document : Nat := 0

def Counts.add (a b : Counts) : Counts :=
  { verification := a.verification + b.verification
    current := a.current + b.current
    application := a.application + b.application
    document := a.document + b.document }

def Counts.report (counts : Counts) : IO Unit := do
  IO.println s!"theorem-count AcornVerif={counts.verification}"
  IO.println s!"theorem-count Acorn={counts.current}"
  IO.println s!"theorem-count NativeApp={counts.application}"
  IO.println s!"theorem-count AcornDocument={counts.document}"
  let total := counts.verification + counts.current + counts.application + counts.document
  IO.println s!"theorem-count total={total}"

def isCompilerCtorIdx (env : Environment) (library : System.FilePath) (owner name : Name)
    (info : ConstantInfo) : IO Bool := do
  if (getExternAttrData? env name).isSome then return false
  let .defn ind := Regula.Load.ctorIdxFormOf env name info | return false
  let implName := Name.str name "_impl"
  unless Compiler.getImplementedBy? env name == some implName do return false
  unless (← AcornBoundaryAudit.declarationOwner env ind) == owner do return false
  let some implInfo := env.find? implName | return false
  unless (← AcornBoundaryAudit.declarationOwner env implName) == owner do return false
  unless Regula.Load.ctorIdxFormOf env implName implInfo == .impl ind do return false
  if (Compiler.getImplementedBy? env implName).isSome then return false
  if (getExternAttrData? env implName).isSome then return false
  let tagOwner ← AcornBoundaryAudit.declarationOwner env `getObjTagNat
  unless (`Init).isPrefixOf tagOwner do return false
  AcornBoundaryAudit.checkOrigin library tagOwner
  return true

def countEnvironment (env : Environment) (owners : Array Name) : IO Counts := do
  let library ← getLibDir (← findSysroot)
  let selected := owners.foldl (fun selected owner => selected.insert owner) ({} : NameSet)
  let mut counts : Counts := {}
  for (name, info) in env.constants do
    let owner ← AcornBoundaryAudit.declarationOwner env name
    if !selected.contains owner then continue
    if (Compiler.getImplementedBy? env name).isSome || (getExternAttrData? env name).isSome then
      unless (← isCompilerCtorIdx env library owner name info) do
        throw (IO.userError s!"{owner}: native replacement for {name}")
    if let .thmInfo _ := info then
      if (`AcornVerif).isPrefixOf owner then
        counts := { counts with verification := counts.verification + 1 }
      else if (`Acorn).isPrefixOf owner then
        counts := { counts with current := counts.current + 1 }
      else if (`NativeApp).isPrefixOf owner then
        counts := { counts with application := counts.application + 1 }
      else if owner == `AcornDocument then
        counts := { counts with document := counts.document + 1 }
      else
        throw (IO.userError s!"{owner}: unexpected project module")
  pure counts

unsafe def inventory : IO Counts := do
  AcornTrackedFiles.admitLeanToolchain
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let modules ← AcornModuleInventory.projectModules
  let shared := modules.filter fun owner => !AcornOwnership.executables.any (·.2 == owner)
  let env ← importModules (shared.map fun owner => { module := owner }) {}
    (leakEnv := true) (loadExts := true)
  let included := modules.filter fun name => (env.getModuleIdx? name).isSome
  let mut counts ← countEnvironment env included
  for name in modules do
    if !included.contains name then
      enableInitializersExecution
      let other ← importModules #[{ module := name }] {} (leakEnv := true) (loadExts := true)
      unless (other.getModuleIdx? name).isSome do
        throw (IO.userError s!"{name}: compiled module did not enter the environment")
      let extra ← countEnvironment other #[name]
      counts := counts.add extra
  pure counts

end AcornTheoremCount
