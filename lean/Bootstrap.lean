/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean

/-! # Provisioned, offline Lake invocation

This bootstrap imports only the pinned Lean toolchain. It maps locked Git
dependencies to existing local paths before Lake loads the workspace. The lock
and provisioned dependency contents are trusted inputs, not downloaded by this
command. The bootstrap is build tooling, outside the application's proof claim.
-/
namespace AcornBootstrap
open Lean

/-- Lift a schema refusal into an explicit command failure. -/
def checked {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

/-- A locked name cannot escape the provisioned package directory. -/
def component (value : String) : IO String := do
  unless !value.isEmpty && value != "." && value != ".." &&
      value.toList.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.') do
    throw (IO.userError s!"unsupported package component: {value}")
  return value

/-- Missing provisioned files are distinct from unreadable or non-regular paths. -/
def regularFileAvailable (path : System.FilePath) : IO Bool := do
  let mut current : System.FilePath := "."
  let parts := path.components.toArray
  for h : i in [:parts.size] do
    current := current / parts[i]
    let expected := if i + 1 == parts.size then IO.FS.FileType.file else .dir
    let metadata ← try some <$> current.symlinkMetadata catch error =>
      if error matches .noFileOrDirectory .. then pure none else throw error
    let some metadata := metadata | return false
    unless metadata.type == expected do
      throw (IO.userError s!"non-regular provisioned path: {current}")
  return true

/-- Mandatory inputs and offline execution reject missing files. -/
def regularFile (path : System.FilePath) : IO Unit := do
  unless ← regularFileAvailable path do
    throw (IO.userError s!"missing provisioned file: {path}")

/-- Admitted local replacements preserve every dependency's locked identity fields. -/
def overrides : IO (Json × Bool) := do
  regularFile "lake-manifest.json"
  let lock ← checked (Json.parse (← IO.FS.readFile "lake-manifest.json"))
  unless (← checked (lock.getObjValAs? String "version")) == "1.2.0" &&
      (← checked (lock.getObjValAs? String "packagesDir")) == ".lake/packages" &&
      (← checked (lock.getObjValAs? String "lakeDir")) == ".lake" do
    throw (IO.userError "unsupported Lake lock layout; provision separately")
  let packages ← checked (lock.getObjValAs? (Array Json) "packages")
  unless !packages.isEmpty do throw (IO.userError "empty locked dependency inventory")
  let mut names : Array String := #[]
  let mut entries : Array Json := #[]
  let mut available := true
  for entry in packages do
    let name ← component (← checked (entry.getObjValAs? String "name"))
    unless !names.contains name && (← checked (entry.getObjValAs? String "type")) == "git" do
      throw (IO.userError "duplicate or unsupported locked dependency")
    names := names.push name
    let config ← component (← checked (entry.getObjValAs? String "configFile"))
    let manifest ← component (← checked (entry.getObjValAs? String "manifestFile"))
    let scope ← checked (entry.getObjValAs? String "scope")
    let inherited ← checked (entry.getObjValAs? Bool "inherited")
    let revision ← checked (entry.getObjValAs? String "rev")
    unless revision.length == 40 && revision.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
      throw (IO.userError s!"invalid locked revision for {name}")
    unless (← checked (entry.getObjVal? "subDir")) == Json.null do
      throw (IO.userError "subdirectory dependencies need explicit provisioning support")
    let dir := s!".lake/packages/{name}"
    -- Inspect every entry even when an earlier dependency is absent: missing
    -- provisioning cannot hide a later schema or filesystem refusal.
    let configAvailable ← regularFileAvailable (dir / config)
    let manifestAvailable ← regularFileAvailable (dir / manifest)
    available := available && configAvailable && manifestAvailable
    entries := entries.push (Json.mkObj [
      ("name", toJson name), ("scope", toJson scope), ("inherited", toJson inherited),
      ("configFile", toJson config), ("manifestFile", toJson manifest),
      ("type", toJson "path"), ("dir", toJson dir)])
  let mathlibAvailable ← regularFileAvailable ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
  let ambient ← try
    let _ ← System.FilePath.symlinkMetadata ".lake/package-overrides.json"
    pure true
  catch error =>
    if error matches .noFileOrDirectory .. then pure false else throw error
  if ambient then
    throw (IO.userError "unbound .lake/package-overrides.json; remove the ambient override")
  return (Json.mkObj [("version", toJson "1.2.0"), ("packages", toJson entries)],
    available && mathlibAvailable)

/-- Invoke Lake only after local dependency admission, with cache fetching disabled. -/
def run (args : List String) : IO UInt32 := do
  unless args == ["provision-status"] || (!args.isEmpty && (#["build", "exe", "env", "query"].contains (args.headD "") ||
      args == ["script", "run", "acornTargets"])) do
    throw (IO.userError "usage: scripts/lean.sh (build|exe|env|query|provision-status) ...")
  regularFile "../verification-profile"
  let profile ← IO.FS.readFile "../verification-profile"
  unless profile == "private\n" || profile == "public\n" do
    throw (IO.userError "verification-profile must be exactly private or public")
  let privateEvidence := if profile == "private\n" then "true" else "false"
  let (contents, available) ← overrides
  -- This read-only status is the launcher's sole provisioning admission:
  -- 0 means ready, 2 means missing dependencies, and every refusal returns 1.
  if args == ["provision-status"] then return if available then 0 else 2
  unless available do
    throw (IO.userError "missing pinned dependencies; run scripts/start.sh --prepare-only")
  let path : System.FilePath := ".lake/acorn-path-packages.json"
  IO.FS.writeFile path (contents.compress ++ "\n")
  let child ← IO.Process.spawn {
    cmd := "lake", args := #["--no-cache", "--reconfigure", s!"--packages={path}", "-K", s!"privateEvidence={privateEvidence}"] ++ args.toArray,
    stdin := .null, env := #[("LAKE_ARTIFACT_CACHE", some "false")] }
  child.wait

end AcornBootstrap

/-- Bootstrap failures are explicit and never trigger dependency provisioning. -/
def main (args : List String) : IO UInt32 := do
  try AcornBootstrap.run args catch error =>
    IO.eprintln s!"offline Lake: {error}"
    return 1
