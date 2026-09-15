/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.Ownership
import Acorn.Host.Viewer.BrowserSchema
import AcornTools.Corpus.Browser

/-! # Compiled declaration and document path admission

Code spans identify maintained declarations or complete path claims. Compiler-owned
names replace lexical declaration inference; IO and Lean environment loading are
the reviewed tooling boundary.
-/
namespace AcornDocument
open Lean

private def externalSymbols : List String := [
  "libc",
  "Vec",
  "Some",
  "None",
  "u8",
  "u16",
  "u32",
  "usize",
  "f32",
  "f64",
  "i64",
  "i128",
  "u32",
  "u64",
  "NonZeroU32",
  "Result",
  "assert",
  "debug_assert",
  "include_str",
  "eprintln",
  "panic",
  "unwrap",
  "expect",
  "todo",
  "unimplemented",
  "unreachable",
  "exit",
  "is_finite",
  "is_power_of_two",
  "unwrap_or_else",
  "read_dir",
  "zip",
  "exp",
  "ln",
  "powf",
  "sqrt",
  "floor",
  "fma",
  "mul_add",
  "spawn",
  "exec",
  "rename",
  "assume",
  "Lean",
  "Float",
  "Float32",
  "Int",
  "Nat",
  "Classical",
  "Quot",
  "propext",
  "IO",
  "decide",
  "native_decide",
  "sorry",
  "ring",
  "SwiftTD",
  "Horde",
  "learn_online_lsvi",
  "JSON",
  "localStorage",
  "requestAnimationFrame",
  "setTimeout",
  "RUSTFLAGS",
  "RUSTDOCFLAGS",
  "CARGO_TARGET_DIR",
  "cargo",
  "pdftotext",
  "ACORN_REGISTRATION_TRUST",
  "warningAsError",
  "autoImplicit",
  "missingDocs"]

private def proseTokens : List String := [
  "assumed",
  "unproven",
  "UNKNOWN",
  "OPEN",
  "no",
  "NaN",
  "paused",
  "COMPACT",
  "LICENSE"]

private def keywords : List String := [
  "crate",
  "self",
  "Self",
  "super",
  "pub",
  "use",
  "as",
  "const",
  "let",
  "unsafe",
  "theorem",
  "axiom",
  "forbid",
  "fn",
  "mod",
  "struct",
  "enum",
  "type",
  "static",
  "trait",
  "impl",
  "match",
  "macro_rules",
  "include",
  "include_str",
  "include_bytes",
  "concat_idents",
  "path",
  "extern",
  "std",
  "core",
  "alloc"]

private def standardMacros : List String := [
  "assert",
  "assert_eq",
  "assert_ne",
  "cfg",
  "column",
  "compile_error",
  "concat",
  "dbg",
  "debug_assert",
  "debug_assert_eq",
  "debug_assert_ne",
  "env",
  "eprint",
  "eprintln",
  "file",
  "format",
  "format_args",
  "line",
  "matches",
  "module_path",
  "option_env",
  "panic",
  "print",
  "println",
  "stringify",
  "todo",
  "unimplemented",
  "unreachable",
  "vec",
  "write",
  "writeln"]

private def fileExtensions : List String := [
  ".md",
  ".rs",
  ".lean",
  ".toml",
  ".json",
  ".txt",
  ".html",
  ".py",
  ".cpp",
  ".ckpt",
  ".log",
  ".yml",
  ".yaml",
  ".lock",
  ".sh",
  ".csv",
  ".ndjson",
  ".olean",
  ".map",
  ".tmp"]

/-- Visible inline code spans; fenced examples are not live document claims. -/
def spans (text : String) : List String := Id.run do
  let mut fenced := false
  let mut result := []
  for line in text.splitOn "\n" do
    if line.trimAscii.toString.startsWith "```" then fenced := !fenced
    else if !fenced then
      let mut inside := false
      for part in line.splitOn "`" do
        if inside && !part.isEmpty then result := part :: result
        inside := !inside
  return result.reverse

private def pathPrefixes : List String := ["src/", "scripts/", "viewer/src/", "viewer/static/",
  "lean/", "gates/", "studies/", "evidence/"]

private def braceExpand (path : String) : Except String (List String) := do
  match path.splitOn "{" with
  | [single] =>
    if single.contains '}' then throw "unbalanced path brace"
    return [single]
  | [head, rest] =>
    let [choices, tail] := rest.splitOn "}" | throw "unbalanced path brace"
    unless !head.contains '}' && !tail.contains '}' do throw "extra path brace"
    return (choices.splitOn ",").map (fun c => head ++ c.trimAscii.toString ++ tail)
  | _ => throw "more than one path brace group"

private def pathClaim (span : String) : IO Unit := do
  let (path, revision, lines) ← match span.splitOn "@" with
    | [plain] => match plain.splitOn ":" with
      | [path] => pure (path, none, none)
      | [path, range] => do
        let bounds := range.splitOn "-"
        let (first, last) ← match bounds with
          | [single] => pure (single, single)
          | [first, last] => pure (first, last)
          | _ => throw (IO.userError "invalid line range")
        let some first := first.toNat? | throw (IO.userError "invalid first line")
        let some last := last.toNat? | throw (IO.userError "invalid last line")
        unless 0 < first && first ≤ last do throw (IO.userError "invalid line interval")
        pure (path, none, some last)
      | _ => throw (IO.userError "invalid path anchor")
    | [path, revision] => do
      unless !revision.isEmpty && revision.toList.all
          (fun c => c.isAlphanum || "_-./".contains c) do throw (IO.userError "invalid revision")
      pure (path, some revision, none)
    | _ => throw (IO.userError "ambiguous path revision")
  unless path.toList.all (fun c => c.isAlphanum || "_./-*{},".contains c) do
    throw (IO.userError "unreadable path claim")
  for path in ← IO.ofExcept (braceExpand path) do
    if revision.isSome then
      throw (IO.userError "archived path references are not part of the maintained source")
    else
      let path := if path.contains '*' then
          String.intercalate "/" (((path.splitOn "*").headD "").splitOn "/").dropLast
        else path
      let kind ← (System.FilePath.mk path).symlinkMetadata
      unless kind.type == .file || kind.type == .dir do throw (IO.userError "path is not regular")
      if let some count := lines then
        unless count ≤ ((← IO.FS.readFile path).splitOn "\n").length do
          throw (IO.userError "line anchor exceeds file")

private def listed (entries : List String) (name : String) : Bool :=
  entries.any fun entry => name == entry || name.startsWith (entry ++ ".") ||
    name.startsWith (entry ++ "::")

private def symbol (span : String) : Option String := do
  guard (span.toList.all (fun c => c.toNat < 128))
  guard (!span.toList.any Char.isWhitespace && !span.contains '/' && !span.contains '-')
  guard (span.toList.head?.any (fun c => c.isAlpha || c == '_'))
  guard (!fileExtensions.any (fun ext => span.endsWith ext))
  guard (!(span.replace "::" "").contains ':')
  guard (!span.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')))
  let mut depth := 0
  let mut chars := []
  for c in span.toList do
    if c == '<' then depth := depth + 1
    else if c == '>' then depth := depth - 1
    else if depth == 0 then chars := c :: chars
  let name := String.ofList chars.reverse
  let name := ((name.splitOn "(").headD name).replace "::" "."
  let name := (name.dropEndWhile (fun c => c == '!')).toString
  guard (name.length > 1 && name.toList.all (fun c => c.isAlphanum || "_.*".contains c))
  guard (!(name.splitOn ".").any (fun part => part.toList.head?.any Char.isDigit))
  return name

/-- Load compiler declarations once, excluding executable `main` collisions.
Only maintained module owners contribute names; imported libraries do not make
an otherwise missing project declaration appear present. -/
unsafe def symbols (selection : Array Name := AcornOwnership.modules) : IO (Std.HashSet String) := do
  let package : System.FilePath := "lean"
  let setup ← IO.Process.output {
    cmd := "./scripts/lean.sh", args := #["env", "lean", "--print-prefix"] }
  unless setup.exitCode == 0 do throw (IO.userError setup.stderr)
  let sysroot : System.FilePath := setup.stdout.trimAscii.toString
  let lock ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (package / "lake-manifest.json")))
  let dependencies ← IO.ofExcept (lock.getObjValAs? (Array Lean.Json) "packages")
  let mut paths := [package / ".lake/build/lib/lean"]
  for dependency in dependencies do
    let name ← IO.ofExcept (dependency.getObjValAs? String "name")
    paths := paths ++ [package / ".lake/packages" / name / ".lake/build/lib/lean"]
  searchPathRef.set (paths ++ [← getLibDir sysroot])
  enableInitializersExecution
  let owners := selection.filter fun owner =>
    !AcornOwnership.executables.any (fun entry => entry.2 == owner)
  let env ← importModules (owners.map fun owner => { module := owner }) {}
    (leakEnv := true) (loadExts := true)
  let mut names : Std.HashSet String := {}
  for (command, owner) in AcornOwnership.executables do
    if selection.contains owner then names := names.insert command
  for owner in selection do
    let parts := owner.toString.splitOn "."
    for start in [:parts.length] do
      names := names.insert (String.intercalate "." (parts.drop start))
  for (key, _) in Acorn.Host.Viewer.browserSchema do names := names.insert key
  for (key, rule) in Acorn.Host.Viewer.browserRules ++ Acorn.Host.Viewer.browserControlRules do
    names := names.insert key
    if let .tags tags := rule then
      for tag in tags do names := names.insert tag
  names := names.insert "main"
  let browser ← AcornBrowserAudit.scripts (← IO.FS.readFile "viewer/static/index.html")
  let words := (String.ofList (browser.toList.map (fun c =>
    if c.isAlphanum || c == '_' || c == '$' then c else ' '))).splitOn " " |>.filter (!·.isEmpty)
  for index in [:words.length] do
    if ["const", "let", "function", "class"].contains (words[index]?.getD "") then
      if let some name := words[index+1]? then names := names.insert name
  for (name, _) in env.constants do
    if let some index := env.getModuleIdxFor? name then
      if let some owner := (env.header.modules[index.toNat]?).map (·.module) then
        if owners.contains owner then
          let parts := name.toString.splitOn "."
          for start in [:parts.length] do
            let suffix := parts.drop start
            for count in [1:suffix.length+1] do
              names := names.insert (String.intercalate "." (suffix.take count))
  return names

private def resolves (names : Std.HashSet String) (name : String) : Bool :=
  let name := name.replace "::" "."
  listed (externalSymbols.map (·.replace "::" ".")) name ||
    (proseTokens ++ keywords ++ standardMacros).contains name || names.contains name ||
    (name.endsWith "_*" && names.toArray.any (fun candidate =>
      candidate.startsWith (name.dropEnd 1).toString))

/-- Every applicable path and declaration claim is checked, reporting all stale
references together; archive paths and external study citations are refused. -/
unsafe def check (documents : Array (String × String))
    (selection : Array Name := AcornOwnership.modules) : IO Unit := do
  let names ← symbols selection
  let mut failures := 0
  for (path, text) in documents do
    for span in (spans text).eraseDups do
      try
        if pathPrefixes.any (fun lead => span.startsWith lead) && !pathPrefixes.contains span then
          pathClaim span
        else if span.startsWith "study:" then
          throw (IO.userError "unresolved study citation")
        else if let some name := symbol span then
          unless resolves names name do throw (IO.userError "unresolved maintained declaration")
      catch error =>
        IO.eprintln s!"{path}: `{span}`: {error}"
        failures := failures + 1
  unless failures == 0 do throw (IO.userError s!"{failures} document reference failures")

end AcornDocument
