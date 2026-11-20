/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean
import AcornTools.Ownership
import AcornTools.Corpus.Browser

/-! # Compiled declaration and document path admission

Code spans identify maintained declarations or complete path claims. Compiler-owned
names replace lexical declaration inference; IO and Lean environment loading are
the reviewed tooling boundary.

The names a document may cite from the viewer's protocol, and the registry of names from
outside the project (`AcornDocument.external`, in the library `AcornDocument`, which any change
may extend), are subjects read from the finished build (`AcornSubjects.read`); this module
imports neither.
-/
namespace AcornDocument
open Lean

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
  "lean/", "site/", "gates/", "studies/", "evidence/"]

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

/-- The value of a text of decimal digits, `0` to `9` and at least one, in positional notation;
nothing for any other text. This is the audit's own reader of a line number: Lean core's
`String.toNat?` also accepts `_` between digits. -/
private def decimal (text : String) : Option Nat :=
  if text.isEmpty then none else
    text.toList.foldlM (fun total c =>
      if '0' ≤ c && c ≤ '9' then some (10 * total + (c.toNat - 48)) else none) 0

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
        let some first := decimal first | throw (IO.userError "invalid first line")
        let some last := decimal last | throw (IO.userError "invalid last line")
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

/-- Derive document symbols from the admitted compiler environment. Every selected
non-entry owner must be present; unrelated imports cannot supply owned names. The names of the
viewer's protocol (the keys of its schema, the names of its page constants, the keys of its rules
and the spellings of their tag rules) are subjects read from that environment. -/
unsafe def symbolsFrom (env : Environment) (selection : Array Name) :
    IO (Std.HashSet String) := do
  let owners := selection.filter fun owner =>
    !AcornOwnership.executables.any (fun entry => entry.2 == owner)
  for owner in owners do
    unless (env.getModuleIdx? owner).isSome do
      throw (IO.userError s!"document symbols: missing compiled owner {owner}")
  let mut names : Std.HashSet String := {}
  for (command, owner) in AcornOwnership.executables do
    if selection.contains owner then names := names.insert command
  for owner in selection do
    let parts := owner.toString.splitOn "."
    for start in [:parts.length] do
      names := names.insert (String.intercalate "." (parts.drop start))
  for term in ["Acorn.Host.Viewer.browserSchema.map Prod.fst",
      "Acorn.Host.Viewer.BrowserConstant.all.map Acorn.Host.Viewer.BrowserConstant.name",
      "(Acorn.Host.Viewer.browserRules ++ Acorn.Host.Viewer.browserControlRules).flatMap \
        (fun entry => entry.1 :: (match entry.2 with \
          | Acorn.Host.Viewer.BrowserRule.tags tags => tags | _ => []))"] do
    for name in ← AcornSubjects.read (List String) env "List String" term do
      names := names.insert name
  names := names.insert "main"
  let browser ← AcornBrowserAudit.scripts (← IO.FS.readFile "viewer/static/index.html")
  let words := (String.ofList (browser.toList.map (fun c =>
    if c.isAlphanum || c == '_' || c == '$' then c else ' '))).splitOn " " |>.filter (!·.isEmpty)
  for index in [:words.length] do
    if ["const", "let", "function", "class"].contains (words[index]?.getD "") then
      if let some name := words[index+1]? then names := names.insert name
  let selected := owners.foldl (fun set owner => set.insert owner) ({} : NameSet)
  for (name, _) in env.constants do
    if let some index := env.getModuleIdxFor? name then
      if let some owner := (env.header.modules[index.toNat]?).map (·.module) then
        if selected.contains owner then
          let parts := name.toString.splitOn "."
          for start in [:parts.length] do
            let suffix := parts.drop start
            for count in [1:suffix.length+1] do
              names := names.insert (String.intercalate "." (suffix.take count))
  return names

/-- Load the compiled declarations of the selected modules once, excluding executable `main`
collisions, for a run of the audit that receives no environment. -/
unsafe def environment (selection : Array Name) : IO Environment := do
  let package : System.FilePath := "lean"
  let setup ← IO.Process.output {
    cmd := "./scripts/lean.sh", args := #["env", "lean", "--print-prefix"] }
  unless setup.exitCode == 0 do throw (IO.userError setup.stderr)
  let sysroot : System.FilePath := setup.stdout.trimAscii.toString
  let lock ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (package / "lake-manifest.json")))
  let dependencies ← IO.ofExcept (lock.getObjValAs? (Array Lean.Json) "packages")
  let mut paths := [package / ".lake/build/lib/lean"]
  for dependency in dependencies do
    -- Lake's checkout directory of the locked name (`PackageEntry.dirName`).
    let name := (← IO.ofExcept (dependency.getObjValAs? String "name")).toName.toString
      (escape := false)
    paths := paths ++ [package / ".lake/packages" / name / ".lake/build/lib/lean"]
  searchPathRef.set (paths ++ [← getLibDir sysroot])
  enableInitializersExecution
  let owners := selection.filter fun owner =>
    !AcornOwnership.executables.any (fun entry => entry.2 == owner)
  importModules (owners.map fun owner => { module := owner }) {}
    (leakEnv := true) (loadExts := true)

private def resolves (external : String → Bool) (names : Std.HashSet String)
    (name : String) : Bool :=
  let name := name.replace "::" "."
  external name ||
    (proseTokens ++ keywords ++ standardMacros).contains name || names.contains name ||
    (name.endsWith "_*" && names.toArray.any (fun candidate =>
      candidate.startsWith (name.dropEnd 1).toString))

/-- Every applicable path and declaration claim is checked, reporting all stale
references together; archive paths and external study citations are refused. Only maintained
module owners of the finished build `env` contribute names; imported libraries do not make an
otherwise missing project declaration appear present. -/
unsafe def check (env : Environment) (documents : Array (String × String))
    (selection : Array Name) : IO Unit := do
  let names ← symbolsFrom env selection
  let external ← AcornSubjects.read (String → Bool) env "String → Bool" "AcornDocument.external"
  let mut failures := 0
  for (path, text) in documents do
    for span in (spans text).eraseDups do
      try
        if pathPrefixes.any (fun lead => span.startsWith lead) && !pathPrefixes.contains span then
          pathClaim span
        else if span.startsWith "study:" then
          throw (IO.userError "unresolved study citation")
        else if let some name := symbol span then
          unless resolves external names name do throw (IO.userError "unresolved maintained declaration")
      catch error =>
        IO.eprintln s!"{path}: `{span}`: {error}"
        failures := failures + 1
  unless failures == 0 do throw (IO.userError s!"{failures} document reference failures")

end AcornDocument
