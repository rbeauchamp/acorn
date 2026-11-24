import Lean.Data.Name
import AcornTools.TrackedFiles

namespace AcornModuleInventory
open Lean

def toolingModules : Array Name := #[`AcornTools, `Bootstrap, `AcornTools.Boundary.Audit, `AcornTools.Boundary.Main, `AcornTools.ModuleInventory, `AcornTools.TrackedFiles,
  `AcornTools.Corpus.Audit, `AcornTools.Corpus.Main, `AcornTools.Boundary.Departures, `AcornTools.Corpus.Browser, `AcornTools.Corpus.Documents, `AcornTools.Corpus.Pins, `AcornTools.Native.Audit, `AcornTools.Native.Resources, `AcornTools.Native.Routes, `AcornTools.OwnershipSource, `AcornTools.Theorems, `AcornTools.TheoremCount, `AcornTools.AxiomPins, `AcornTools.Ownership, `AcornTools.OwnershipAudit, `AcornTools.Gate, `AcornTools.Intent, `AcornTools.Frame]

def modulesUnder (root : System.FilePath) (skipped : Array String)
    (expectedPrefix : String) (requireClean : Bool := true) : IO (Array Name) := do
  let paths ← AcornTrackedFiles.listTracked root expectedPrefix requireClean
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

def allModules (package : System.FilePath := ".") (requireClean : Bool := true) : IO (Array Name) :=
  modulesUnder package #[".lake", "lake-packages", ".git", ".DS_Store", "lakefile.lean"]
    "lean/" requireClean

def libraryModule (name : Name) : Bool :=
  #[`Acorn, `AcornVerif, `NativeApp, `AcornDocument, `Entry].any (·.isPrefixOf name)

def siteModules (requireClean : Bool := true) : IO (Array Name) :=
  modulesUnder (System.FilePath.mk ".." / "site") #[".lake", "_out", ".DS_Store"] "site/"
    requireClean

def projectModules : IO (Array Name) := do
  return (← allModules).filter (!toolingModules.contains ·)

def decisionRegistry : Name := `Acorn.Decisions

def nativeModule (owner : Name) : Bool :=
  owner != decisionRegistry && ((`Acorn).isPrefixOf owner || (`NativeApp).isPrefixOf owner ||
    (`Entry).isPrefixOf owner)

end AcornModuleInventory
