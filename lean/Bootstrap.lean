/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic

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

/-- Interpreted `lean --run` still executes `main` after header-time warnings, such as
a deprecated import, that `warningAsError` does not reach. This file must elaborate
under the launcher options with no message at all before any command proceeds. -/
def silentElaboration : IO Unit := do
  let output ← IO.Process.output {
    cmd := (← IO.appPath).toString, stdin := .null,
    args := #["-DwarningAsError=true", "-DautoImplicit=false", "Bootstrap.lean"] }
  unless output.exitCode == 0 && output.stdout.isEmpty && output.stderr.isEmpty do
    throw (IO.userError s!"Bootstrap.lean elaboration reported messages:\n{output.stdout}{output.stderr}")

/-- Lake runs with cache fetching disabled and the admitted local dependencies.
`--wfail` makes any logged warning fail the build, including header-time warnings
(for example a deprecated import) that `warningAsError` does not reach. -/
def lake (overrides : System.FilePath) (args : Array String) : IO.Process.SpawnArgs := {
  cmd := "lake", args := #["--no-cache", "--wfail", s!"--packages={overrides}"] ++ args,
  stdin := .null, env := #[("LAKE_ARTIFACT_CACHE", some "false")] }

/-- The proof bridge is the single owner of its FloatLib imports, and the two decision
registries of their Regula imports. FloatLib publishes no build cache, and verification
must not compile a dependency inside its deadline. Lake itself decides readiness: with
`--no-build` it exits 3 unless every artifact and trace in the import closure of the
`floatlibBridge` and `regulaInterface` targets is current, so no list of expected files
is kept here. -/
def dependencyImportsBuilt (overrides : System.FilePath) : IO Bool := do
  let output ← IO.Process.output
    (lake overrides #["build", "--no-build", "floatlibBridge", "regulaInterface"])
  if output.exitCode == 0 then return true
  if output.exitCode == 3 then return false
  throw (IO.userError
    s!"Lake could not decide dependency provisioning:\n{output.stdout}{output.stderr}")

/-- Invoke Lake only after local dependency admission. -/
def run (args : List String) : IO UInt32 := do
  silentElaboration
  unless args == ["provision-status"] ||
      (!args.isEmpty && (#["build", "exe", "env", "query", "lint"].contains (args.headD "") ||
      args == ["script", "run", "acornTargets"])) do
    throw (IO.userError "usage: scripts/lean.sh (build|exe|env|query|lint|provision-status) ...")
  let (contents, available) ← overrides
  let path : System.FilePath := ".lake/acorn-path-packages.json"
  -- Lake validates its configuration trace against source and toolchain changes;
  -- explicit dependency overrides are resolved again on every invocation.
  if available then IO.FS.writeFile path (contents.compress ++ "\n")
  let ready ← if available then dependencyImportsBuilt path else pure false
  -- This status is the launcher's sole provisioning admission: 0 means ready,
  -- 2 means missing dependencies, and every refusal returns 1. It builds nothing,
  -- writes only the override file above and asks Lake whether the FloatLib modules
  -- the bridge imports and the Regula modules the decision registries import are
  -- current.
  if args == ["provision-status"] then return if ready then 0 else 2
  unless ready do
    throw (IO.userError "missing pinned dependencies; run scripts/start.sh --prepare-only")
  let child ← IO.Process.spawn (lake path args.toArray)
  child.wait

end AcornBootstrap

/-- Bootstrap failures are explicit and never trigger dependency provisioning. -/
def main (args : List String) : IO UInt32 := do
  try AcornBootstrap.run args catch error =>
    IO.eprintln s!"offline Lake: {error}"
    return 1
