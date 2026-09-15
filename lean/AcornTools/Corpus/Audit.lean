/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AuditPins
import AcornTools.ModuleInventory
import AcornTools.Corpus.Documents
import AcornTools.Corpus.Pins
import AcornTools.Corpus.Browser

/-! # Maintained corpus admission

Language boundaries, document references and scientific publications are checked
against the complete regular-file corpus and explicit evidence references. Source
and compiled Lean policy remain AcornTools.Boundary.Audit's responsibility.
-/
namespace AcornCorpus

private def require (legal : Bool) (message : String) : IO Unit :=
  unless legal do throw (IO.userError message)

private def excluded : List String := [".git", "target", "viewer/target", "gates/target",
  "lean/.lake", "lean/lake-packages", "session"]

/-- The complete corpus is traversed without symlink or unreadable-file fallback. -/
def files : IO (Array String) := do
  let mut pending := #[""]
  let mut result := #[]
  while !pending.isEmpty do
    let some dir := pending.back? | throw (IO.userError "corpus lost pending directory")
    pending := pending.pop
    let root : System.FilePath := if dir.isEmpty then "." else dir
    for entry in ← root.readDir do
      let path := if dir.isEmpty then entry.fileName else dir ++ "/" ++ entry.fileName
      unless entry.fileName == ".DS_Store" || excluded.contains path do
        match (← entry.path.symlinkMetadata).type with
        | .dir => pending := pending.push path
        | .file => result := result.push path
        | _ => throw (IO.userError s!"corpus rejects nonregular entry {path}")
  return result.qsort (· < ·)

private def pythonToken (text : String) : Bool :=
  (text.splitOn " ").any fun word =>
    ["python", "python2", "python3", "pypy", "pypy3"].contains word || word.startsWith "python3."

private def language (archivalFile : String → Bool) (path : String) : IO Unit := do
  unless archivalFile path do
    let bytes ← IO.FS.readBinFile path
    let ext := ((System.FilePath.mk path).extension.getD "").toLower
    require (!["rs", "py", "pyw", "pyi", "pyc", "pyo", "ipynb", "pyz", "tar", "zip", "gz", "tgz", "xz", "bz2", "7z",
      "rb", "pl", "pm", "lua", "go", "java", "cpp", "cc", "cxx", "h", "hpp", "swift", "jl", "r", "php", "bash", "zsh", "fish"].contains ext)
      s!"{path}: source/archive outside maintained Lean or inventoried evidence boundary"
    if ext == "c" then
      require (path == "lean/os/checkpoint-sync.c")
        s!"{path}: C source outside reviewed fsync primitive"
    if ["js", "ts", "jsx", "tsx", "mjs", "cjs"].contains ext then
      require (path.startsWith "viewer/static/") s!"{path}: browser code outside observer assets"
    if let some text := String.fromUTF8? bytes then
      let first := (text.splitOn "\n").headD ""
      let shell := ext == "sh" || first.startsWith "#!/bin/sh" || first.startsWith "#!/bin/bash"
      let infrastructure := ["scripts/", ".github/", ".cursor/"].any (fun p => path.startsWith p)
      require (!shell || infrastructure) s!"{path}: shell outside infrastructure"
      require (!first.startsWith "#!" || (shell && infrastructure)) s!"{path}: unreviewed interpreter entry"
      if shell || ["yml", "yaml", "toml"].contains ext then
        for line in text.splitOn "\n" do
          unless line.trimAscii.toString.startsWith "#" do
            let tokens := String.ofList (line.toList.map fun c => if c.isAlphanum || c == '_' || c == '.' then c else ' ')
            require (!pythonToken tokens) s!"{path}: Python interpreter in maintained infrastructure"

/-- Maintained prose owners, including the private dossier presentation surface. -/
def prose (path : String) : Bool :=
  (["README.md", "AGENTS.md", "plans/roadmap.md"].contains path) ||
  (path.startsWith "docs/" && path.endsWith ".md" &&
    !((System.FilePath.mk path).fileName.getD "").startsWith "_") ||
  (path.startsWith "studies/" && ((path.endsWith "/README.md" && (path.splitOn "/").length ≤ 3) ||
    (path.endsWith "/protocol.md" && (path.splitOn "/").length == 5)))

private def numberAfter (lead : String) (text : String) : List String :=
  (text.splitOn lead).drop 1 |>.filterMap fun part =>
    let digits := (part.takeWhile Char.isDigit).toString
    if digits.isEmpty then none else some (lead ++ digits)

private def visible (text : String) : IO (List String) := do
  let mut comments := false
  let mut plain := []
  let mut rest := text.toList
  for _ in [:rest.length] do
    if rest.isEmpty then break
    if !comments && "<!--".toList.isPrefixOf rest then
      comments := true; rest := rest.drop 4
    else if comments && "-->".toList.isPrefixOf rest then
      comments := false; rest := rest.drop 3
    else
      if !comments then
        if let some c := rest.head? then plain := c :: plain
      rest := rest.drop 1
  require (!comments) "unterminated HTML comment"
  let mut fence : Option (Char × Nat) := none
  let mut lines := []
  for line in (String.ofList plain.reverse).splitOn "\n" do
    let trimmed := (line.dropWhile (· == ' ')).toString
    if line.length - trimmed.length > 3 || trimmed.startsWith "\t" then continue
    let first := trimmed.toList.head?
    let width := (trimmed.toList.takeWhile (fun c => some c == first)).length
    match fence with
    | some (kind, minimum) =>
      if first == some kind && minimum ≤ width && (trimmed.drop width).toString.trimAscii.isEmpty then fence := none
    | none =>
      if (first == some '`' || first == some '~') && width ≥ 3 then
        if let some c := first then fence := some (c, width)
      else lines := trimmed :: lines
  return lines.reverse

private def refutations (lines : List String) (heading : String → Bool) : IO Unit := do
  let mut pending : Option String := none
  let mut found := false
  for line in lines ++ ["# end"] do
    if line.startsWith "#" then
      if let some key := pending then require found s!"{key}: missing Refutation attempt field"
      pending := if heading line then some line else none
      found := false
    else if line.contains "*Refutation attempt.*" then found := true

/-- The same register obligations apply to prepared and installed public prose. -/
def priorArtTexts (reviewText design frontier : String) : IO Unit := do
  let review ← visible reviewText
  let entries := review.filterMap fun line =>
    if line.startsWith "### PAR-" then (numberAfter "PAR-" line).head? else none
  let anchors := (numberAfter "[PAR-" design).map (fun s => (s.drop 1).toString)
  require (!entries.isEmpty && entries.all anchors.contains && anchors.all entries.contains)
    "DESIGN prior-art anchors differ from admitted entries"
  let mut active := false
  let mut sections := 0
  let mut keys := []
  for line in review do
    if line == "### Current default qualification" then
      sections := sections + 1; active := true
    else if line.startsWith "#" then active := false
    else if active && line.startsWith "| PAR-" then
      let fields := (line.splitOn "|").drop 1 |>.dropLast |>.map (·.trimAscii.toString)
      require (fields.length == 5 && fields.all (!·.isEmpty)) "incomplete default qualification row"
      let key := fields.headD ""
      require (!keys.contains key) s!"duplicate qualification {key}"
      require (["provisional-reference", "research-only", "qualified", "demoted"].contains (fields[1]?.getD ""))
        s!"{key}: unknown default qualification"
      keys := key :: keys
  require (sections == 1 && keys.all entries.contains && entries.all keys.contains)
    "default qualification inventory differs from admitted prior art"
  refutations review (fun line => line.startsWith "### PAR-" || line.startsWith "### REJ-")
  refutations (← visible frontier)
    (fun line => line.startsWith "## F" && (line.drop 4).toString.toList.head?.any Char.isDigit)

/-- Shared maintained-source checks. Historical exemptions must be supplied by an
admitted private registry; source-only checks refuse dossier citations and archived path references.
Filesystem discovery remains complete in either case. -/
unsafe def check (evidence : AcornDocument.EvidenceReferences := {})
    (archivalFile : String → Bool := fun _ => false) (documentsOnly : Bool := false) : IO Unit := do
  let paths ← files
  unless documentsOnly do
    for path in paths do language archivalFile path
  priorArtTexts (← IO.FS.readFile "docs/prior-art-review.md")
    (← IO.FS.readFile "docs/design.md") (← IO.FS.readFile "docs/frontier.md")
  let documents ← (paths.filter prose).mapM fun (path : String) => do
    pure (path, ← IO.FS.readFile path)
  AcornBrowserAudit.check
  AcornPinAudit.check documents
  AcornDocument.check evidence documents
  IO.println (if documentsOnly then "corpus: document references and prior-art qualifications admitted"
    else "corpus: language, document references and prior-art qualifications admitted")

end AcornCorpus
