import VersoManual
import AcornSite.Markdown
import AcornDocs

open Verso.Genre Manual

def pages : List (String × Verso.Doc.Part Manual × String) :=
  [("site/AcornDocs/Verification.lean", %doc AcornDocs.Verification, "docs/verification.md")]

def markdown (write : Bool) : IO Bool := do
  let mut current := true
  for (source, document, kept) in pages do
    let path := System.FilePath.mk ".." / kept
    match AcornSite.Markdown.page source document with
    | .error refusal =>
      IO.eprintln s!"site: {source}: {refusal}"
      current := false
    | .ok text =>
      if write then
        IO.FS.writeFile path text
      else if (← IO.FS.readFile path) != text then
        IO.eprintln s!"site: {kept} differs from the rendering of {source}; ./scripts/verify.sh site write writes the rendering"
        current := false
  return current

def main (args : List String) : IO UInt32 := do
  let write ← match args with
    | [] => pure false
    | ["write"] => pure true
    | _ =>
      IO.eprintln "usage: lean --run Main.lean [write]"
      return 1
  unless ← markdown write do return 1
  manualMain (%doc AcornDocs) (options := []) (config := {
    emitTeX := false, emitHtmlSingle := .no, emitHtmlMulti := .immediately, htmlDepth := 1,
    sourceLink := some "https://github.com/rbeauchamp/acorn",
    issueLink := some "https://github.com/rbeauchamp/acorn/issues" })
