/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.ModuleInventory
import AcornTools.Ownership

/-! # Ownership admission before application compilation -/
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

end AcornOwnershipAudit
