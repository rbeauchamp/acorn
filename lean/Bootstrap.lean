import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic

namespace AcornBootstrap
open Lean

def checked {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

def component (value : String) : IO String := do
  unless !value.isEmpty && value != "." && value != ".." &&
      value.toList.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.') do
    throw (IO.userError s!"unsupported package component: {value}")
  return value

def packageDir (name : String) : IO String :=
  component (name.toName.toString (escape := false))

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

def regularFile (path : System.FilePath) : IO Unit := do
  unless ← regularFileAvailable path do
    throw (IO.userError s!"missing provisioned file: {path}")

def overrides : IO (Json × Bool) := do
  regularFile "lake-manifest.json"
  let lock ← checked (Json.parse (← IO.FS.readFile "lake-manifest.json"))
  unless (← checked (lock.getObjValAs? String "version")) == "1.3.0" &&
      (← checked (lock.getObjValAs? String "name")) == "acorn" &&
      (← checked (lock.getObjValAs? String "packagesDir")) == ".lake/packages" &&
      (← checked (lock.getObjValAs? String "lakeDir")) == ".lake" do
    throw (IO.userError "unsupported Lake lock layout; provision separately")
  let packages ← checked (lock.getObjValAs? (Array Json) "packages")
  unless !packages.isEmpty do throw (IO.userError "empty locked dependency inventory")
  let mut seenNames : Array Name := #[]
  let mut names : Array String := #[]
  let mut entries : Array Json := #[]
  let mut available := true
  for entry in packages do
    let name ← checked (entry.getObjValAs? String "name")
    let decoded := name.toName
    let directory ← packageDir name
    unless !seenNames.contains decoded && !names.contains directory &&
        (← checked (entry.getObjValAs? String "type")) == "git" do
      throw (IO.userError "duplicate or unsupported locked dependency")
    seenNames := seenNames.push decoded
    names := names.push directory
    let config ← component (← checked (entry.getObjValAs? String "configFile"))
    let manifest ← component (← checked (entry.getObjValAs? String "manifestFile"))
    let scope ← checked (entry.getObjValAs? String "scope")
    let inherited ← checked (entry.getObjValAs? Bool "inherited")
    let url ← checked (entry.getObjValAs? String "url")
    unless !url.isEmpty do
      throw (IO.userError s!"empty locked URL for {name}")
    let revision ← checked (entry.getObjValAs? String "rev")
    unless revision.length == 40 && revision.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
      throw (IO.userError s!"invalid locked revision for {name}")
    unless (← checked (entry.getObjVal? "subDir")) == Json.null do
      throw (IO.userError "subdirectory dependencies need explicit provisioning support")
    let dir := s!".lake/packages/{directory}"
    let configAvailable ← regularFileAvailable (dir / config)
    let manifestAvailable ← regularFileAvailable (dir / manifest)
    let gitMeta? ← try some <$> (System.FilePath.mk dir / ".git").symlinkMetadata catch error =>
      if error matches .noFileOrDirectory .. then pure none else throw error
    if let some gm := gitMeta? then
      unless gm.type == .dir || gm.type == .file do
        throw (IO.userError s!"non-regular provisioned path: {dir}/.git")
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

def silentElaboration : IO Unit := do
  let output ← IO.Process.output {
    cmd := (← IO.appPath).toString, stdin := .null,
    args := #["-DwarningAsError=true", "-DautoImplicit=false", "Bootstrap.lean"] }
  unless output.exitCode == 0 && output.stdout.isEmpty && output.stderr.isEmpty do
    throw (IO.userError s!"Bootstrap.lean elaboration reported messages:\n{output.stdout}{output.stderr}")

def lake (overrides : System.FilePath) (args : Array String) : IO.Process.SpawnArgs := {
  cmd := "lake",
  args := #["-f", "lakefile.lean", "--no-cache", "--wfail", s!"--packages={overrides}"] ++ args,
  stdin := .null, env := #[("LAKE_ARTIFACT_CACHE", some "false")] }

def dependencyImportsBuilt (overrides : System.FilePath) : IO Bool := do
  let output ← IO.Process.output
    (lake overrides #["build", "--no-build", "floatlibBridge", "regulaInterface",
      "leanIntentBridge", "leanIntentNative"])
  if output.exitCode == 0 then return true
  if output.exitCode == 3 then return false
  throw (IO.userError
    s!"Lake could not decide dependency provisioning:\n{output.stdout}{output.stderr}")

private def stripNewline (text : String) : String :=
  (text.dropEndWhile fun c => c == '\n' || c == '\r').toString

private def isHexOid (value : String) : Bool :=
  (value.length == 40 || value.length == 64) &&
    value.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

private def splitFirstChar (s : String) (sep : Char) : String × Option String :=
  match s.splitOn (String.singleton sep) with
  | [] => ("", none)
  | [only] => (only, none)
  | head :: rest => (head, some (String.intercalate (String.singleton sep) rest))

private def longLakeOptsWithArg : Array String := #[
  "--package", "--service", "--scope", "--repo", "--platform", "--toolchain", "--rev",
  "--max-revs", "--log-level", "--fail-level",
  "--linters", "--lint-only", "--checks", "--only", "--add-downstream",
  "--add-public-downstream", "--config", "--from-export", "--challenge-from-export",
  "--solution-from-export"
]

private def optionFuel (xs : List String) : Nat :=
  3 * (xs.foldl (fun acc s => acc + s.length + 1) 1) + 1

private inductive OptionStep where
  | stop
  | positional (arg : String) (rest : List String)
  | disallowed (opt : String)
  | next (rest : List String)

private def stepLakeOption (arg : String) (rest : List String) : OptionStep :=
  if arg.isEmpty then
    .next rest
  else if arg.length > 1 && arg.startsWith "-" then
    if arg.startsWith "--" then
      let (lhs, eqVal?) := splitFirstChar arg '='
      let afterEq := match eqVal? with | some v => v :: rest | none => rest
      let (optName, spVal?) := splitFirstChar lhs ' '
      let nextArgs := match spVal? with | some v => v :: afterEq | none => afterEq
      if optName == "--" then
        .stop
      else if optName == "--file" || optName == "--dir" || optName == "--packages" then
        .disallowed optName
      else if longLakeOptsWithArg.contains optName then
        .next (nextArgs.drop 1)
      else
        .next nextArgs
    else
      let chars := arg.toList
      match chars[1]? with
      | none => .stop
      | some c =>
        let nextArgs :=
          if chars.length == 2 then rest
          else match chars[2]? with
            | some '=' => (arg.drop 3).toString :: rest
            | some ' ' => (arg.drop 2).trimAsciiStart.toString :: rest
            | _ => (arg.drop 2).toString :: rest
        if c == 'f' || c == 'd' then
          .disallowed s!"-{c}"
        else if c == 'K' || c == 'o' then
          .next (nextArgs.drop 1)
        else
          .next nextArgs
  else
    .positional arg rest

private def scanLakeOptions : Nat → List String → Bool → IO Unit
  | 0, _, _ => throw (IO.userError "Lake option validation exceeded step bound")
  | _ + 1, [], _ => pure ()
  | fuel + 1, arg :: rest, stopAtPositional =>
    match stepLakeOption arg rest with
    | .stop => pure ()
    | .disallowed opt =>
      throw (IO.userError s!"disallowed Lake override option in bootstrap invocation: {opt}")
    | .next remaining => scanLakeOptions fuel remaining stopAtPositional
    | .positional _ remaining =>
      if stopAtPositional then pure () else scanLakeOptions fuel remaining stopAtPositional

private def validateCallerArgs (args : List String) : IO Unit := do
  if args == ["provision-status"] ||
      args == ["script", "run", "acornTargets"] ||
      args == ["script", "run", "intentLibraries"] then
    return
  match args with
  | "build" :: rest | "query" :: rest =>
    scanLakeOptions (optionFuel rest) rest false
  | "exe" :: rest | "env" :: rest =>
    scanLakeOptions (optionFuel rest) rest true
  | _ =>
    throw (IO.userError "usage: scripts/lean.sh (build|exe|env|query|provision-status) ...")

private def toLakeName (s : String) : Name :=
  if s.toName.isAnonymous then Name.mkSimple s else s.toName

private def normalizeExeTarget (spec : String) : Option String :=
  match spec.splitOn "/" with
  | [target] => some ((toLakeName target).toString (escape := false))
  | [pkg, target] =>
    let pkg := if pkg.startsWith "@" then (pkg.drop 1).toString else pkg
    if pkg.isEmpty || toLakeName pkg == `acorn then
      some ((toLakeName target).toString (escape := false))
    else
      none
  | _ => none

private def findExeTargetAux : Nat → List String → Option (String × List String)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, arg :: rest =>
    match stepLakeOption arg rest with
    | .stop | .disallowed _ => none
    | .next remaining => findExeTargetAux fuel remaining
    | .positional target remaining =>
      (normalizeExeTarget target).map (·, remaining)

private def findExeTarget (args : List String) : Option (String × List String) :=
  findExeTargetAux (optionFuel args) args

private def requiresCleanHead (args : List String) : Bool :=
  match args with
  | "exe" :: rest =>
    match findExeTarget rest with
    | some ("acorn-gates", ["site", "write"]) => false
    | some ("acorn-gates", ["diagnostics"]) => false
    | some ("acorn-gates", _) => true
    | some ("frame-check", "print" :: _) => false
    | some ("frame-check", _) => true
    | some ("lean-boundary-audit", _) | some ("native-audit", _)
    | some ("ownership-audit", _) | some ("corpus-audit", _)
    | some ("theorem-count", _) | some ("intent-check", _) => true
    | _ => false
  | _ => false

private def admitTrackedHelper (requireClean : Bool) : IO System.FilePath := do
  let topOut ← IO.Process.output {
    cmd := "git", args := #["--no-optional-locks", "-C", ".", "rev-parse", "--show-toplevel"],
    stdin := .null }
  unless topOut.exitCode == 0 do
    throw (IO.userError s!"git rev-parse --show-toplevel failed: {topOut.stderr}")
  let prefixOut ← IO.Process.output {
    cmd := "git", args := #["--no-optional-locks", "-C", ".", "rev-parse", "--show-prefix"],
    stdin := .null }
  unless prefixOut.exitCode == 0 do
    throw (IO.userError s!"git rev-parse --show-prefix failed: {prefixOut.stderr}")
  unless stripNewline prefixOut.stdout == "lean/" do
    throw (IO.userError "unexpected git prefix in lean directory")
  let repoRoot := System.FilePath.mk (stripNewline topOut.stdout)
  unless (← IO.FS.realPath (repoRoot / "lean")) == (← IO.FS.realPath ".") do
    throw (IO.userError "git root mismatch in lean directory")
  let scriptsMeta ← (repoRoot / "scripts").symlinkMetadata
  unless scriptsMeta.type == .dir do
    throw (IO.userError "scripts is not a real directory")
  let helper := repoRoot / "scripts/tracked-files.sh"
  let helperMeta ← helper.symlinkMetadata
  unless helperMeta.type == .file do
    throw (IO.userError "scripts/tracked-files.sh is not a regular file")
  let stageOut ← IO.Process.output {
    cmd := "git",
    args := #["--no-optional-locks", "--literal-pathspecs", "-C", repoRoot.toString,
      "-c", "core.quotePath=false", "ls-files", "--stage", "-z", "--", "scripts/tracked-files.sh"],
    stdin := .null }
  unless stageOut.exitCode == 0 do
    throw (IO.userError s!"git ls-files failed for scripts/tracked-files.sh: {stageOut.stderr}")
  let records := (stageOut.stdout.splitOn (String.singleton (Char.ofNat 0))).filter (!·.isEmpty)
  let [record] := records | throw (IO.userError "scripts/tracked-files.sh is not tracked")
  let [metaPart, path] := record.splitOn "\t"
    | throw (IO.userError s!"malformed git ls-files record: {record}")
  let [mode, oid, stage] := metaPart.splitOn " "
    | throw (IO.userError s!"malformed git ls-files metadata: {metaPart}")
  unless (mode == "100644" || mode == "100755") && stage == "0" &&
      path == "scripts/tracked-files.sh" && isHexOid oid do
    throw (IO.userError "scripts/tracked-files.sh is not a stage-0 tracked regular file")
  if requireClean then
    let headOut ← IO.Process.output {
      cmd := "git", args := #["--no-optional-locks", "-C", repoRoot.toString,
        "rev-parse", "--verify", "-q", "HEAD"], stdin := .null }
    unless headOut.exitCode == 0 do
      throw (IO.userError "HEAD commit is unavailable")
    let cachedOut ← IO.Process.output {
      cmd := "git", args := #["--no-optional-locks", "-C", repoRoot.toString,
        "diff-index", "--cached", "--quiet", "--ignore-submodules=none", "HEAD", "--",
        "scripts/tracked-files.sh"], stdin := .null }
    unless cachedOut.exitCode == 0 do
      throw (IO.userError "scripts/tracked-files.sh has staged changes differing from HEAD")
    let wtOut ← IO.Process.output {
      cmd := "git", args := #["--no-optional-locks", "-C", repoRoot.toString,
        "-c", "core.symlinks=true", "-c", "core.fsmonitor=false",
        "diff", "--no-ext-diff", "--no-textconv", "--quiet", "--ignore-submodules=none",
        "HEAD", "--", "scripts/tracked-files.sh"], stdin := .null }
    unless wtOut.exitCode == 0 do
      throw (IO.userError "scripts/tracked-files.sh has working-copy changes differing from HEAD")
    let flagOut ← IO.Process.output {
      cmd := "git", args := #["--no-optional-locks", "--literal-pathspecs", "-C", repoRoot.toString,
        "-c", "core.quotePath=false", "ls-files", "-v", "-z", "--", "scripts/tracked-files.sh"],
      stdin := .null }
    let vrecords := (flagOut.stdout.splitOn (String.singleton (Char.ofNat 0))).filter (!·.isEmpty)
    unless flagOut.exitCode == 0 && vrecords == ["H scripts/tracked-files.sh"] do
      throw (IO.userError "scripts/tracked-files.sh has non-clean Git index flags")
  return repoRoot

private def syncTrackedConfigTrace (requireClean : Bool) : IO Unit := do
  let repoRoot ← admitTrackedHelper requireClean
  let helper := repoRoot / "scripts/tracked-files.sh"
  let helperArgs := if requireClean then
    #["sync-config", "--clean", repoRoot.toString]
  else
    #["sync-config", repoRoot.toString]
  let out ← IO.Process.output { cmd := helper.toString, args := helperArgs, stdin := .null }
  unless out.exitCode == 0 do
    throw (IO.userError (out.stderr ++ out.stdout).trimAscii.toString)

private def byteHex (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList
  let hi := digits[(b >>> 4).toNat]?.getD '0'
  let lo := digits[(b &&& 0x0f).toNat]?.getD '0'
  String.ofList [hi, lo]

private def randomHex8 : IO String := do
  let bytes ← IO.getRandomBytes 8
  let mut out := ""
  for b in bytes.data do
    out := out ++ byteHex b
  return out

private def writeFileAtomicExclusive (path : System.FilePath) (text : String) : IO Unit := do
  let pid ← IO.Process.getPID
  for _ in [:16] do
    let suffix ← randomHex8
    let tmp : System.FilePath := s!"{path}.{pid}.{suffix}.tmp"
    let handle? ← try some <$> IO.FS.Handle.mk tmp .writeNew catch error =>
      if error matches .alreadyExists .. then pure none else throw error
    if let some h := handle? then
      try
        h.putStr text
        h.flush
        IO.FS.rename tmp path
      catch error =>
        try IO.FS.removeFile tmp catch _ => pure ()
        throw error
      return
  throw (IO.userError s!"unable to allocate exclusive temporary file for {path}")

def run (args : List String) : IO UInt32 := do
  silentElaboration
  validateCallerArgs args
  syncTrackedConfigTrace (requiresCleanHead args)
  let (contents, available) ← overrides
  let path : System.FilePath := ".lake/acorn-path-packages.json"
  if available then
    let text := contents.compress ++ "\n"
    let current ← try some <$> IO.FS.readFile path catch _ => pure none
    unless current == some text do
      writeFileAtomicExclusive path text
  let ready ← if available then dependencyImportsBuilt path else pure false
  if args == ["provision-status"] then return if ready then 0 else 2
  unless ready do
    throw (IO.userError "missing pinned dependencies; scripts/start.sh --prepare-only provisions them, and in work on a change to Acorn, CONTRIBUTING.md (\"Running a program\") states the conditions for running it")
  let child ← IO.Process.spawn (lake path args.toArray)
  child.wait

end AcornBootstrap

def main (args : List String) : IO UInt32 := do
  try AcornBootstrap.run args catch error =>
    IO.eprintln s!"offline Lake: {error}"
    return 1
