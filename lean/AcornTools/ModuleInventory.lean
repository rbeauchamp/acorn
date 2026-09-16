/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean

/-! # Shared fail-closed maintained-module inventory -/
namespace AcornModuleInventory
open Lean

/-- Reviewed verification/bootstrap modules are explicit trust boundaries. New
root tools do not acquire an exemption merely by living outside `Acorn`. -/
def toolingModules : Array Name := #[`AcornTools, `Bootstrap, `AcornTools.Boundary.Audit, `AcornTools.Boundary.Main, `AcornTools.ModuleInventory,
  `AcornTools.Corpus.Audit, `AcornTools.Corpus.Main, `AcornTools.Boundary.Departures, `AcornTools.Corpus.Browser, `AcornTools.Corpus.Documents, `AcornTools.Corpus.Pins, `AcornTools.Native.Audit, `AcornTools.Native.Resources, `AcornTools.Native.Routes, `AcornTools.TheoremCount, `AcornTools.Ownership, `AcornTools.OwnershipAudit, `AcornTools.Gate]

/-- Discover all maintained Lean sources, including root tools and new directories.
Only the package's generated/dependency directories and Lake configuration are
excluded. Traversal and metadata errors are fatal; symlinks are refused. -/
def allModules : IO (Array Name) := do
  let mut pending : Array System.FilePath := #["."]
  let mut modules : Array Name := #[]
  while !pending.isEmpty do
    let some dir := pending.back?
      | throw (IO.userError "module inventory lost its pending directory")
    pending := pending.pop
    unless (← dir.symlinkMetadata).type == .dir do
      throw (IO.userError s!"{dir}: expected a maintained module directory")
    for entry in ← dir.readDir do
      if dir == System.FilePath.mk "." &&
          #[".lake", "lake-packages", ".git", ".DS_Store", "lakefile.lean"].contains entry.fileName then
        continue
      match (← entry.path.symlinkMetadata).type with
      | .dir => pending := pending.push entry.path
      | .file =>
        if entry.path.extension == some "lean" then
          let parts := (entry.path.withExtension "").components.filter (· != ".")
          modules := modules.push (parts.foldl Name.str Name.anonymous)
      | _ => throw (IO.userError s!"{entry.path}: non-regular maintained source")
  pure (modules.qsort fun a b => a.toString < b.toString)

/-- Application and proof counts exclude the explicitly reviewed gate tooling. -/
def projectModules : IO (Array Name) := do
  return (← allModules).filter (!toolingModules.contains ·)

/-- Every current native module needs an actual object and compiler trace, even
when no executable imports its library root. -/
def nativeModule (owner : Name) : Bool :=
  (`Acorn).isPrefixOf owner || (`NativeApp).isPrefixOf owner

end AcornModuleInventory
