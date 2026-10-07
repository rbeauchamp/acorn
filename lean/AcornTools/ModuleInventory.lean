/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean.Data.Name

/-! # Shared fail-closed maintained-module inventory -/
namespace AcornModuleInventory
open Lean

/-- Reviewed verification/bootstrap modules are explicit trust boundaries. New
root tools do not acquire an exemption merely by living outside `Acorn`. -/
def toolingModules : Array Name := #[`AcornTools, `Bootstrap, `AcornTools.Boundary.Audit, `AcornTools.Boundary.Main, `AcornTools.ModuleInventory,
  `AcornTools.Corpus.Audit, `AcornTools.Corpus.Main, `AcornTools.Boundary.Departures, `AcornTools.Corpus.Browser, `AcornTools.Corpus.Documents, `AcornTools.Corpus.Pins, `AcornTools.Native.Audit, `AcornTools.Native.Resources, `AcornTools.Native.Routes, `AcornTools.OwnershipSource, `AcornTools.Theorems, `AcornTools.TheoremCount, `AcornTools.Ownership, `AcornTools.OwnershipAudit, `AcornTools.Gate]

/-- Lean sources below `root`, named relative to it. `skipped` lists the entries of `root`
itself that are generated, dependency or Lake configuration files. Traversal and metadata
errors are fatal; symlinks are refused. -/
def modulesUnder (root : System.FilePath) (skipped : Array String) : IO (Array Name) := do
  let mut pending : Array (System.FilePath × Name) := #[(root, .anonymous)]
  let mut modules : Array Name := #[]
  while !pending.isEmpty do
    let some (dir, owner) := pending.back?
      | throw (IO.userError "module inventory lost its pending directory")
    pending := pending.pop
    unless (← dir.symlinkMetadata).type == .dir do
      throw (IO.userError s!"{dir}: expected a maintained module directory")
    for entry in ← dir.readDir do
      if owner.isAnonymous && skipped.contains entry.fileName then continue
      match (← entry.path.symlinkMetadata).type with
      | .dir => pending := pending.push (entry.path, owner.str entry.fileName)
      | .file =>
        if entry.path.extension == some "lean" then
          modules := modules.push
            (owner.str ((System.FilePath.mk entry.fileName).withExtension "").toString)
      | _ => throw (IO.userError s!"{entry.path}: non-regular maintained source")
  pure (modules.qsort fun a b => a.toString < b.toString)

/-- Discover all maintained Lean sources of this package, including root tools and new
directories. Only the package's generated/dependency directories and Lake configuration
are excluded. -/
def allModules : IO (Array Name) :=
  modulesUnder "." #[".lake", "lake-packages", ".git", ".DS_Store", "lakefile.lean"]

/-- Discover the Lean sources of the documentation site, the separate Lake package in
`site/`. Its Lake outputs and the rendered pages are excluded. -/
def siteModules : IO (Array Name) :=
  modulesUnder (System.FilePath.mk ".." / "site") #[".lake", "_out", ".DS_Store"]

/-- Application and proof counts exclude the explicitly reviewed gate tooling. -/
def projectModules : IO (Array Name) := do
  return (← allModules).filter (!toolingModules.contains ·)

/-- The registration leaf of the executing library: Regula executable contracts about the
executing definitions, and their decision registrations. It belongs to the `Acorn` library
because Regula decides a registered function against the contracts of the function's own
library. No module may import it, so no entry point links what it declares: specification
predicates, one decision procedure for such a predicate and two closed values. -/
def decisionRegistry : Name := `Acorn.Decisions

/-- Every current native module needs an actual object and compiler trace, even
when no executable imports its library root. The decision registry is no native module:
no module imports it, so it is linked into no entry point. -/
def nativeModule (owner : Name) : Bool :=
  owner != decisionRegistry && ((`Acorn).isPrefixOf owner || (`NativeApp).isPrefixOf owner)

end AcornModuleInventory
