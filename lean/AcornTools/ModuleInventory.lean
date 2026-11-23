/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean.Data.Name
import AcornTools.TrackedFiles

/-! # Shared fail-closed maintained-module inventory -/
namespace AcornModuleInventory
open Lean

/-- Reviewed verification/bootstrap modules are explicit trust boundaries. New
root tools do not acquire an exemption merely by living outside `Acorn`. -/
def toolingModules : Array Name := #[`AcornTools, `Bootstrap, `AcornTools.Boundary.Audit, `AcornTools.Boundary.Main, `AcornTools.ModuleInventory, `AcornTools.TrackedFiles,
  `AcornTools.Corpus.Audit, `AcornTools.Corpus.Main, `AcornTools.Boundary.Departures, `AcornTools.Corpus.Browser, `AcornTools.Corpus.Documents, `AcornTools.Corpus.Pins, `AcornTools.Native.Audit, `AcornTools.Native.Resources, `AcornTools.Native.Routes, `AcornTools.OwnershipSource, `AcornTools.Theorems, `AcornTools.TheoremCount, `AcornTools.AxiomPins, `AcornTools.Ownership, `AcornTools.OwnershipAudit, `AcornTools.Gate, `AcornTools.Intent, `AcornTools.Frame]

def modulesUnder (root : System.FilePath) (skipped : Array String)
    (expectedPrefix : Option String := none) : IO (Array Name) := do
  let paths ← AcornTrackedFiles.listTracked root expectedPrefix
  let mut modules : Array Name := #[]
  for path in paths do
    let parts := path.splitOn "/"
    if parts.head?.any skipped.contains then continue
    if (System.FilePath.mk path).extension == some "lean" then
      let stem := ((System.FilePath.mk (parts.getLastD "")).withExtension "").toString
      let modParts := parts.dropLast ++ [stem]
      if modParts.any (·.isEmpty) then
        throw (IO.userError s!"empty module component in {path}")
      modules := modules.push (modParts.foldl Name.str .anonymous)
  if modules.isEmpty then
    throw (IO.userError s!"no tracked Lean modules under {root}")
  pure (modules.qsort fun a b => a.toString < b.toString)

def allModules (package : System.FilePath := ".") : IO (Array Name) :=
  modulesUnder package #[".lake", "lake-packages", ".git", ".DS_Store", "lakefile.lean"]
    (some "lean/")

/-- The libraries whose modules Lake's globs assign: `Acorn`, `AcornVerif`, `NativeApp` and
`AcornDocument`, the default targets whose modules the Regula audit claims, and `Entry`,
the executables' roots, which it does not claim. A source below one of these roots needs no
entry in a written list. -/
def libraryModule (name : Name) : Bool :=
  #[`Acorn, `AcornVerif, `NativeApp, `AcornDocument, `Entry].any (·.isPrefixOf name)

def siteModules : IO (Array Name) :=
  modulesUnder (System.FilePath.mk ".." / "site") #[".lake", "_out", ".DS_Store"] (some "site/")

/-- Application and proof counts exclude the explicitly reviewed gate tooling. -/
def projectModules : IO (Array Name) := do
  return (← allModules).filter (!toolingModules.contains ·)

/-- The registration leaf of the executing library: Regula executable contracts about the executing
definitions, and their decision registrations (`Regula.RegisteredDecision`). It belongs to the
`Acorn` library, so the proof claim covers it, and the ownership audit requires a contract with a
decision kind for each function it registers. No module may import it, so no entry point links what
it declares: theorems, specification predicates, the structures of the arguments of the functions
with a dependent type, and closed values that are inputs of the witnesses of kinds. -/
def decisionRegistry : Name := `Acorn.Decisions

/-- Every current native module needs an actual object and compiler trace, even
when no executable imports its library root. The decision registry is no native module:
no module imports it, so it is linked into no entry point. -/
def nativeModule (owner : Name) : Bool :=
  owner != decisionRegistry && ((`Acorn).isPrefixOf owner || (`NativeApp).isPrefixOf owner ||
    (`Entry).isPrefixOf owner)

end AcornModuleInventory
