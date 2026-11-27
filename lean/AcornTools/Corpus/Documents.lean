import Lean
import AcornDocument
import Acorn.Digits
import AcornTools.Ownership
import Acorn.Host.Viewer.BrowserSchema
import Acorn.Host.Viewer.BrowserStore
import AcornTools.TrackedFiles

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

private def leanLiterals : List String := [
  "true",
  "false"]

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
  "alloc",
  "def",
  "abbrev",
  "opaque",
  "inductive",
  "structure",
  "class",
  "instance",
  "where",
  "extends",
  "deriving",
  "private",
  "protected",
  "noncomputable",
  "partial",
  "partial_fixpoint",
  "termination_by",
  "decreasing_by",
  "namespace",
  "section",
  "open",
  "import",
  "expose",
  "meta",
  "module",
  "prelude"]

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

private structure TrackedIndex where
  files : Std.HashSet String
  dirs : Std.HashSet String

private def trackedIndex (tracked : Array String) : TrackedIndex := Id.run do
  let mut files : Std.HashSet String := {}
  let mut dirs : Std.HashSet String := {}
  for path in tracked do
    files := files.insert path
    let parts := path.splitOn "/"
    let mut cur := ""
    for part in parts.dropLast do
      cur := if cur.isEmpty then part else cur ++ "/" ++ part
      dirs := dirs.insert cur
  return { files, dirs }

private def allowedBuildDir (path : String) : Bool :=
  ["lean/.lake", "lean/.lake/packages"].contains path

private def pathClaim (tracked : TrackedIndex) (span : String) : IO Unit := do
  let (path, revision, lines) ← match span.splitOn "@" with
    | [plain] => match plain.splitOn ":" with
      | [path] => pure (path, none, none)
      | [path, range] => do
        let bounds := range.splitOn "-"
        let (first, last) ← match bounds with
          | [single] => pure (single, single)
          | [first, last] => pure (first, last)
          | _ => throw (IO.userError "invalid line range")
        let some first := Acorn.Digits.read first | throw (IO.userError "invalid first line")
        let some last := Acorn.Digits.read last | throw (IO.userError "invalid last line")
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
    else if path.contains '*' then
      unless lines.isNone do throw (IO.userError "line anchor on directory wildcard")
      let dir := String.intercalate "/" (((path.splitOn "*").headD "").splitOn "/").dropLast
      unless tracked.dirs.contains dir || allowedBuildDir dir do
        throw (IO.userError s!"path is not tracked: {dir}")
      AcornTrackedFiles.ensureRegularDir "." dir
    else
      let hasTrailingSlash := path.endsWith "/"
      let normalized := if hasTrailingSlash then (path.dropEndWhile (· == '/')).toString else path
      discard (AcornTrackedFiles.checkComponents normalized)
      if hasTrailingSlash then
        unless lines.isNone do throw (IO.userError "line anchor on directory")
        unless tracked.dirs.contains normalized || allowedBuildDir normalized do
          throw (IO.userError s!"directory is not tracked: {normalized}")
        AcornTrackedFiles.ensureRegularDir "." normalized
      else if let some count := lines then
        unless tracked.files.contains normalized do
          throw (IO.userError s!"file is not tracked: {normalized}")
        AcornTrackedFiles.ensureRegular "." normalized
        unless count ≤ ((← IO.FS.readFile normalized).splitOn "\n").length do
          throw (IO.userError "line anchor exceeds file")
      else if tracked.files.contains normalized then
        AcornTrackedFiles.ensureRegular "." normalized
      else if tracked.dirs.contains normalized || allowedBuildDir normalized then
        AcornTrackedFiles.ensureRegularDir "." normalized
      else
        throw (IO.userError s!"path is not tracked: {normalized}")

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

private def libraryRoots : List String := ["Init", "Std", "Lean"]

private def openLibraryRoots : List String := ["Std", "Lean"]

private def isLeanLibraryModule (owner : Name) : Bool :=
  #[`Init, `Std, `Lean].any (·.isPrefixOf owner)

private def isLeanInitModule (owner : Name) : Bool :=
  (`Init).isPrefixOf owner

private def isLowerIdent (s : String) : Bool :=
  match s.toList with
  | c :: _ => 'a' ≤ c && c ≤ 'z'
  | [] => false

private def isUpperIdent (s : String) : Bool :=
  match s.toList with
  | c :: _ => 'A' ≤ c && c ≤ 'Z'
  | [] => false

private def pushNameComponents : Name → Array String → Array String
  | .anonymous, acc => acc
  | .str parent part, acc => (pushNameComponents parent acc).push part
  | .num parent n, acc => (pushNameComponents parent acc).push (toString n)

private def insertQualifiedParts (names : Std.HashSet String) (name : Name) :
    Std.HashSet String := Id.run do
  let parts := pushNameComponents name #[]
  let mut names := names
  for start in [:parts.size] do
    if let some head := parts[start]? then
      let mut current := head
      names := names.insert current
      for stop in [start + 1 : parts.size] do
        if let some part := parts[stop]? then
          current := current ++ "." ++ part
          names := names.insert current
  return names

private def insertRootPrefixes (names : Std.HashSet String) (name : Name) :
    Std.HashSet String := Id.run do
  let parts := pushNameComponents name #[]
  let mut names := names
  let mut current := ""
  for part in parts do
    current := if current.isEmpty then part else current ++ "." ++ part
    names := names.insert current
  return names

private def insertLibraryConstant (library : Std.HashSet String) (name : Name) :
    Std.HashSet String :=
  let parts := pushNameComponents name #[]
  match parts.toList with
  | [] => library
  | [single] => library.insert ("_root_." ++ single)
  | _ => library.insert (String.intercalate "." parts.toList)

private def insertLibraryShorthand (shorthand : Std.HashSet String) (parts : List String) :
    Std.HashSet String :=
  match parts with
  | root :: head :: next :: rest =>
    if openLibraryRoots.contains root then
      shorthand.insert (String.intercalate "." (head :: next :: rest))
    else
      shorthand
  | _ => shorthand

private def insertQualifiedField (fields : Std.HashSet String) (ownerStruct fieldName : Name) :
    Std.HashSet String := Id.run do
  let structParts := pushNameComponents ownerStruct #[]
  let fieldParts := pushNameComponents fieldName #[]
  if structParts.isEmpty || fieldParts.isEmpty then
    return fields
  let fieldSuffix := String.intercalate "." fieldParts.toList
  let mut fields := fields
  for start in [:structParts.size] do
    let ownerSuffix :=
      String.intercalate "." (structParts.extract start structParts.size).toList
    fields := fields.insert (ownerSuffix ++ "." ++ fieldSuffix)
  return fields

private def insertLibraryField (fields : Std.HashSet String) (ownerStruct fieldName : Name) :
    Std.HashSet String :=
  let structParts := pushNameComponents ownerStruct #[]
  let fieldParts := pushNameComponents fieldName #[]
  if structParts.isEmpty || fieldParts.isEmpty then
    fields
  else
    let fullStruct := String.intercalate "." structParts.toList
    let fieldSuffix := String.intercalate "." fieldParts.toList
    let qualified := fullStruct ++ "." ++ fieldSuffix
    if structParts.size == 1 then
      (fields.insert qualified).insert ("_root_." ++ qualified)
    else
      fields.insert qualified

private def insertLibraryFieldShorthand (shorthand : Std.HashSet String)
    (ownerStruct fieldName : Name) : Std.HashSet String :=
  let structParts := pushNameComponents ownerStruct #[]
  let fieldParts := pushNameComponents fieldName #[]
  if structParts.size < 2 || fieldParts.isEmpty then
    shorthand
  else
    insertLibraryShorthand shorthand (structParts.toList ++ fieldParts.toList)

private def insertStructureFields (env : Environment) (structName : Name)
    (includePrivate : Bool) (insertField : Name → Std.HashSet String → Std.HashSet String)
    (fields : Std.HashSet String) : Std.HashSet String := Id.run do
  let mut fields := fields
  for fieldName in getStructureFieldsFlattened env structName do
    if !fieldName.isInternalDetail then
      if let some fieldOwner := findField? env structName fieldName then
        if let some fieldInfo := getFieldInfo? env fieldOwner fieldName then
          if includePrivate || !isPrivateName fieldInfo.projFn then
            fields := insertField fieldName fields
  return fields

structure SymbolInventory where
  acorn : Std.HashSet String := {}
  acornFields : Std.HashSet String := {}
  library : Std.HashSet String := {}
  libraryFields : Std.HashSet String := {}
  libraryShorthand : Std.HashSet String := {}
  preludeRootTypes : Std.HashSet String := {}
  preludeOps : Std.HashSet String := {}

def symbolsFrom (env : Environment) (selection : Array Name) : IO SymbolInventory := do
  let owners := selection.filter fun owner =>
    !AcornOwnership.executables.any (fun entry => entry.2 == owner)
  for owner in owners do
    unless (env.getModuleIdx? owner).isSome do
      throw (IO.userError s!"document symbols: missing compiled owner {owner}")
  let mut acorn : Std.HashSet String := {}
  let mut acornFields : Std.HashSet String := {}
  let mut library : Std.HashSet String := {}
  let mut libraryFields : Std.HashSet String := {}
  let mut libraryShorthand : Std.HashSet String := {}
  let mut preludeRootTypes : Std.HashSet String := {}
  let mut preludeOps : Std.HashSet String := {}
  for (command, owner) in AcornOwnership.executables do
    if selection.contains owner then acorn := acorn.insert command
  for owner in selection do
    let parts := owner.toString.splitOn "."
    for start in [:parts.length] do
      acorn := acorn.insert (String.intercalate "." (parts.drop start))
  for imported in env.header.modules do
    if isLeanLibraryModule imported.module then
      library := insertRootPrefixes library imported.module
  for (key, _) in Acorn.Host.Viewer.browserSchema do acorn := acorn.insert key
  for constant in Acorn.Host.Viewer.BrowserConstant.all do acorn := acorn.insert constant.name
  for (key, rule) in Acorn.Host.Viewer.browserRules ++ Acorn.Host.Viewer.browserControlRules do
    acorn := acorn.insert key
    if let .tags tags := rule then
      for tag in tags do acorn := acorn.insert tag
  acorn := acorn.insert "main"
  let selected := owners.foldl (fun set owner => set.insert owner) ({} : NameSet)
  let mut usedByAcorn : NameSet := {}
  for (name, info) in env.constants do
    if let some index := env.getModuleIdxFor? name then
      if let some owner := (env.header.modules[index.toNat]?).map (·.module) then
        if selected.contains owner then
          let userName := (privateToUserName? name).getD name
          acorn := insertQualifiedParts acorn userName
          if isStructure env name then
            acornFields := insertStructureFields env name true
              (fun fieldName acc => insertQualifiedField acc userName fieldName) acornFields
          usedByAcorn := usedByAcorn.union info.type.getUsedConstantsAsSet
          if let some value := info.value? then
            usedByAcorn := usedByAcorn.union value.getUsedConstantsAsSet
  let mut initOpCandidates : Std.HashMap String (Option Name) := {}
  for (name, _) in env.constants do
    if let some index := env.getModuleIdxFor? name then
      if let some owner := (env.header.modules[index.toNat]?).map (·.module) then
        let inSelected := selected.contains owner
        if !inSelected && isLeanLibraryModule owner && !isPrivateName name &&
            !name.isInternalDetail && !isNoConfusion env name then
          library := insertLibraryConstant library name
          if isStructure env name then
            libraryFields := insertStructureFields env name false
              (fun fieldName acc => insertLibraryField acc name fieldName) libraryFields
          if usedByAcorn.contains name then
            libraryShorthand := insertLibraryShorthand libraryShorthand
              (pushNameComponents name #[]).toList
            if isStructure env name then
              libraryShorthand := insertStructureFields env name false
                (fun fieldName acc => insertLibraryFieldShorthand acc name fieldName)
                libraryShorthand
          if isLeanInitModule owner then
            let parts := pushNameComponents name #[]
            if parts.size == 1 then
              if let some leaf := parts[0]? then
                if isUpperIdent leaf && usedByAcorn.contains name then
                  preludeRootTypes := preludeRootTypes.insert leaf
            if parts.size == 1 || parts.size == 2 then
              if let some leaf := parts.back? then
                if isLowerIdent leaf then
                  initOpCandidates := match initOpCandidates.get? leaf with
                    | none => initOpCandidates.insert leaf (some name)
                    | some _ => initOpCandidates.insert leaf none
  for (leaf, candidate) in initOpCandidates do
    if let some name := candidate then
      if usedByAcorn.contains name then
        preludeOps := preludeOps.insert leaf
  return {
    acorn, acornFields, library, libraryFields, libraryShorthand,
    preludeRootTypes, preludeOps
  }

unsafe def symbols (selection : Array Name) : IO SymbolInventory := do
  let package : System.FilePath := "lean"
  AcornTrackedFiles.ensureTrackedRegular "." "" "scripts/lean.sh"
  let setup ← IO.Process.output {
    cmd := "./scripts/lean.sh", args := #["env", "lean", "--print-prefix"] }
  unless setup.exitCode == 0 do throw (IO.userError setup.stderr)
  let sysroot : System.FilePath := setup.stdout.trimAscii.toString
  AcornTrackedFiles.ensureTrackedRegular "." "" "lean/lake-manifest.json"
  let lock ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile (package / "lake-manifest.json")))
  let dependencies ← IO.ofExcept (lock.getObjValAs? (Array Lean.Json) "packages")
  let mut paths := [package / ".lake/build/lib/lean"]
  let mut seenDeps : Std.HashSet String := {}
  for dependency in dependencies do
    let name := (← IO.ofExcept (dependency.getObjValAs? String "name")).toName.toString
      (escape := false)
    if name.isEmpty || name == "." || name == ".." || seenDeps.contains name ||
        !name.toList.all (fun c => c.isAlphanum || c == '-' || c == '_' || c == '.') then
      throw (IO.userError s!"duplicate or unsupported locked dependency directory: {name}")
    seenDeps := seenDeps.insert name
    paths := paths ++ [package / ".lake/packages" / name / ".lake/build/lib/lean"]
  searchPathRef.set (paths ++ [← getLibDir sysroot])
  enableInitializersExecution
  let owners := selection.filter fun owner =>
    !AcornOwnership.executables.any (fun entry => entry.2 == owner)
  let env ← importModules (owners.map fun owner => { module := owner }) {}
    (leakEnv := true) (loadExts := true)
  symbolsFrom env selection

private def resolves (inventory : SymbolInventory) (name : String) : Bool :=
  let name := name.replace "::" "."
  if name.endsWith "_*" then
    inventory.acorn.toArray.any (fun candidate =>
      candidate.startsWith (name.dropEnd 1).toString)
  else if name.contains '.' then
    external name ||
      inventory.acorn.contains name ||
      inventory.acornFields.contains name ||
      inventory.library.contains name ||
      inventory.libraryFields.contains name ||
      inventory.libraryShorthand.contains name
  else
    external name || leanLiterals.contains name ||
      (proseTokens ++ keywords ++ standardMacros).contains name ||
      inventory.acorn.contains name ||
      inventory.preludeRootTypes.contains name ||
      inventory.preludeOps.contains name ||
      (libraryRoots.contains name && inventory.library.contains name)

unsafe def check (documents : Array (String × String)) (selection : Array Name)
    (tracked : Array String) (env? : Option Environment := none) : IO Unit := do
  let index := trackedIndex tracked
  let inventory ← match env? with
    | some env => symbolsFrom env selection
    | none => symbols selection
  let mut failures := 0
  for (path, text) in documents do
    for span in (spans text).eraseDups do
      try
        if pathPrefixes.any (fun lead => span.startsWith lead) && !pathPrefixes.contains span then
          pathClaim index span
        else if span.startsWith "study:" then
          throw (IO.userError "unresolved study citation")
        else if let some name := symbol span then
          unless resolves inventory name do throw (IO.userError "unresolved maintained declaration")
      catch error =>
        IO.eprintln s!"{path}: `{span}`: {error}"
        failures := failures + 1
  unless failures == 0 do throw (IO.userError s!"{failures} document reference failures")

end AcornDocument
