/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.Boundary.Audit
import AcornTools.Ownership

/-!
# Compiler-backed theorem inventory

Count `.thmInfo` declarations by the module index recorded in compiled Lean
environments, and refuse a native replacement on any project declaration. Source
filenames discover the owned modules, including modules outside either library
root's import closure; source text never decides whether a declaration is a
theorem. Imported Lean and Mathlib theorems are excluded by their owning module,
even if their declaration names resemble project names.

The inventory includes compiler-generated auxiliary theorem declarations and
private theorems. Counts report this complete scope of compiled declarations.
The axioms of each declaration, project axioms, and `unsafe` and `partial`
declarations are checked by the Regula audit of the claimed libraries, not here.
The replacement refusal stays: `AcornVerif` claims report execution, where
Regula's RG3002 (https://rbeauchamp.github.io/regula/v/0.10.0/rules/RG3002/)
reports a replacement and does not refuse it.
-/

namespace AcornTheoremCount

open Lean

/-- Counts of compiled declarations whose owning module belongs to each project. -/
structure Counts where
  /-- Theorem declarations owned by `AcornVerif` modules. -/
  verification : Nat := 0
  /-- Theorem declarations owned by current executable `Acorn` modules. -/
  current : Nat := 0
  /-- Theorem declarations owned by native application bootstrap modules. -/
  application : Nat := 0

/-- Sum disjoint owning-module inventories. -/
def Counts.add (a b : Counts) : Counts :=
  { verification := a.verification + b.verification
    current := a.current + b.current
    application := a.application + b.application }

/-- Report declaration scope, not a correctness score. -/
def Counts.report (counts : Counts) : IO Unit := do
  IO.println s!"theorem-count AcornVerif={counts.verification}"
  IO.println s!"theorem-count Acorn={counts.current}"
  IO.println s!"theorem-count NativeApp={counts.application}"
  IO.println s!"theorem-count total={counts.verification + counts.current + counts.application}"

/-- Count the selected owning modules in one compiled environment. A declaration of a
selected module with `implemented_by` or `extern` is refused. -/
def countEnvironment (env : Environment) (owners : Array Name) : IO Counts := do
  let selected := owners.foldl (fun selected owner => selected.insert owner) ({} : NameSet)
  let mut counts : Counts := {}
  for (name, info) in env.constants do
    let owner ← AcornBoundaryAudit.declarationOwner env name
    if !selected.contains owner then continue
    if (Compiler.getImplementedBy? env name).isSome || (getExternAttrData? env name).isSome then
      throw (IO.userError s!"{owner}: native replacement for {name}")
    if let .thmInfo _ := info then
      if (`AcornVerif).isPrefixOf owner then
        counts := { counts with verification := counts.verification + 1 }
      else if (`Acorn).isPrefixOf owner then
        counts := { counts with current := counts.current + 1 }
      else if (`NativeApp).isPrefixOf owner then
        counts := { counts with application := counts.application + 1 }
      else
        throw (IO.userError s!"{owner}: unexpected project module")
  pure counts

/-- Import every non-entry project module together, including isolated leaves. Executable
modules are imported separately because their top-level `main` names overlap.
Each owning module is counted once, regardless of how many roots import it. -/
unsafe def inventory : IO Counts := do
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
