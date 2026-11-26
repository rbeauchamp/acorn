import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic
import AcornTools.ModuleInventory
import AcornTools.Ownership
import AcornTools.TrackedFiles

namespace AcornOwnershipAudit
open Lean

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError s!"ownership: {message}")

def siteModuleInventory (requireClean : Bool := true) : IO Unit := do
  let actual ← AcornModuleInventory.siteModules requireClean
  require (AcornOwnership.siteModules.toList.eraseDups.length == AcornOwnership.siteModules.size)
    "duplicate registered site module"
  for name in actual do
    require (AcornOwnership.siteModules.contains name) s!"unowned site module {name}"
  for name in AcornOwnership.siteModules do
    require (actual.contains name) s!"stale site module owner {name}"

def siteSources (requireClean : Bool := true) : IO Unit := do
  siteModuleInventory requireClean
  let args := if requireClean then #["admit-site", "--clean", ".."] else #["admit-site", ".."]
  AcornTrackedFiles.runTrackedHelper ".." args requireClean

def sources : IO (Array Name) := do
  siteSources
  let actual ← AcornModuleInventory.allModules
  let tools := AcornModuleInventory.toolingModules
  require (actual.toList.eraseDups.length == actual.size) "duplicate discovered module"
  require (tools.toList.eraseDups.length == tools.size) "duplicate registered module"
  for name in actual do
    require (AcornModuleInventory.libraryModule name || tools.contains name)
      s!"unowned maintained module {name}"
  for name in tools do
    require (actual.contains name) s!"stale module owner {name}"
  return actual

def inventory (modules : Array Name) : IO (Array (String × Name) × Array String) := do
  let output ← IO.Process.output (← AcornTrackedFiles.bootstrapProcess
    #["script", "run", "acornTargets"])
  require (output.exitCode == 0) s!"Lake target discovery failed: {output.stderr}"
  let values ← IO.ofExcept ((← IO.ofExcept (Json.parse output.stdout)).getArr?)
  let mut actual := #[]
  let mut waiting := #[]
  for value in values do
    let target ← IO.ofExcept (value.getObjValAs? String "target")
    let owner ← IO.ofExcept (value.getObjValAs? String "module")
    actual := actual.push (target, owner.toName)
    if ← IO.ofExcept (value.getObjValAs? Bool "needs") then waiting := waiting.push target
  require (actual.toList.eraseDups.length == actual.size) "duplicate Lake executable"
  for entry in actual do
    require (AcornOwnership.executables.contains entry) s!"unowned Lake executable {entry}"
  for entry in AcornOwnership.executables do
    require (actual.contains entry) s!"stale executable owner {entry}"
    require (modules.contains entry.2) s!"unmaintained executable root {entry}"
  return (actual, waiting)

def targets (modules : Array Name) : IO (Array (String × Name)) :=
  return (← inventory modules).1

end AcornOwnershipAudit
