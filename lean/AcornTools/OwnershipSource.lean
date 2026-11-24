/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic
import AcornTools.ModuleInventory
import AcornTools.Ownership
import AcornTools.TrackedFiles

/-! # Ownership admission before application compilation -/
namespace AcornOwnershipAudit
open Lean

/-- AcornTools.Ownership refusals are fatal and identify the missing contract. -/
def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError s!"ownership: {message}")

/-- The Git dependencies a Lake lock manifest names, each with its URL and locked revision. -/
def lockedRevisions (manifest : System.FilePath) : IO (Array (String × String × String)) := do
  let lock ← IO.ofExcept (Json.parse (← IO.FS.readFile manifest))
  let mut locked := #[]
  for entry in ← IO.ofExcept (lock.getObjValAs? (Array Json) "packages") do
    if (← IO.ofExcept (entry.getObjValAs? String "type")) == "git" then
      locked := locked.push (← IO.ofExcept (entry.getObjValAs? String "name"),
        ← IO.ofExcept (entry.getObjValAs? String "url"),
        ← IO.ofExcept (entry.getObjValAs? String "rev"))
  return locked

/-- The documentation site in `site/` is a separate Lake workspace with the same closed
source inventory. It keeps its dependency checkouts in this package's `.lake/packages`, so
it must lock every dependency of this package to the same URL and revision: with a different
lock, building one workspace would move the other's checkout. -/
def siteSources : IO Unit := do
  let actual ← AcornModuleInventory.siteModules
  require (AcornOwnership.siteModules.toList.eraseDups.length == AcornOwnership.siteModules.size)
    "duplicate registered site module"
  for name in actual do
    require (AcornOwnership.siteModules.contains name) s!"unowned site module {name}"
  for name in AcornOwnership.siteModules do
    require (actual.contains name) s!"stale site module owner {name}"
  AcornTrackedFiles.ensureTrackedRegular ".." (some "") "site/lakefile.toml"
  AcornTrackedFiles.ensureTrackedRegular ".." (some "") "site/lean-toolchain"
  AcornTrackedFiles.ensureTrackedRegular ".." (some "") "site/lake-manifest.json"
  AcornTrackedFiles.ensureTrackedRegular "." (some "lean/") "lake-manifest.json"
  let site : System.FilePath := System.FilePath.mk ".." / "site" / "lake-manifest.json"
  let lock ← IO.ofExcept (Json.parse (← IO.FS.readFile site))
  require ((lock.getObjValAs? String "version").toOption == some "1.3.0")
    "site/lake-manifest.json must use version 1.3.0"
  require ((lock.getObjValAs? String "packagesDir").toOption == some "../lean/.lake/packages")
    "site/lake-manifest.json must keep its packages in lean/.lake/packages"
  let mut sawAcorn := false
  for entry in ← IO.ofExcept (lock.getObjValAs? (Array Json) "packages") do
    let ty ← IO.ofExcept (entry.getObjValAs? String "type")
    let name ← IO.ofExcept (entry.getObjValAs? String "name")
    if ty == "git" then
      continue
    else if ty == "path" && name == "acorn" && !sawAcorn then
      sawAcorn := true
      require ((entry.getObjValAs? String "dir").toOption == some "../lean" &&
          (entry.getObjValAs? String "configFile").toOption == some "lakefile.lean" &&
          (entry.getObjValAs? String "manifestFile").toOption == some "lake-manifest.json" &&
          (entry.getObjValAs? String "scope").toOption == some "" &&
          (entry.getObjValAs? Bool "inherited").toOption == some false &&
          (entry.getObjValAs? Bool "copy").toOption == some false)
        "site/lake-manifest.json acorn path entry mismatch"
    else
      require false s!"unsupported site/lake-manifest.json package entry: {name}"
  require sawAcorn "site/lake-manifest.json missing acorn path entry"
  let toml ← IO.FS.readFile (System.FilePath.mk ".." / "site" / "lakefile.toml")
  require (toml.contains "name = \"acorn\"\npath = \"../lean\"")
    "site/lakefile.toml must require acorn at ../lean"
  let shared ← lockedRevisions site
  for (name, url, revision) in ← lockedRevisions "lake-manifest.json" do
    require (shared.contains (name, url, revision))
      s!"site/lake-manifest.json does not lock {name} to {url} at {revision}"

/-- Every discovered source is a module of a library whose modules Lake's globs assign
(`AcornModuleInventory.libraryModule`) or a listed tool module, and a stale tool entry is
refused. -/
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

/-- Read Lake's evaluated executable configuration through the offline bootstrap. The
second component names the executables whose configuration lists a target in `needs`.
`modules` are the discovered sources, which hold every executable root. -/
def inventory (modules : Array Name) : IO (Array (String × Name) × Array String) := do
  let output ← IO.Process.output {
    cmd := "lean", args := #["-DwarningAsError=true", "-DautoImplicit=false", "--run",
      "Bootstrap.lean", "script", "run", "acornTargets"] }
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

/-- Lake's evaluated executables, admitted against the registered inventory. -/
def targets (modules : Array Name) : IO (Array (String × Name)) :=
  return (← inventory modules).1

end AcornOwnershipAudit
