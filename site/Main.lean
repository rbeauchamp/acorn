/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import VersoManual
import AcornSite.Markdown
import AcornDocs

/-! # Documentation renderer

Run in Lean's interpreter from `site/` by the site step of verification
(`./scripts/verify.sh site`), after the documents are built. With no argument it requires
each kept Markdown file to equal the Markdown rendering of its document, then renders the
pages as HTML into `_out`; Verso's rendering fails on an unresolved cross-reference. With
`write` it writes the Markdown files first. Nothing is published.

It is not a linked executable: linking would compile the native code of every proof
module a document imports, and of the Mathlib modules below them.
-/

open Verso.Genre Manual

/-- Each ported document: its Verso source, its elaborated value and the Markdown file kept
for readers of the repository. Paths are relative to the repository root. -/
def pages : List (String × Verso.Doc.Part Manual × String) :=
  [("site/AcornDocs/Verification.lean", %doc AcornDocs.Verification, "docs/verification.md")]

/-- Write, or compare with, the kept Markdown rendering of every ported document. -/
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
        IO.eprintln s!"site: {kept} differs from the rendering of {source}; run ./scripts/verify.sh site write"
        current := false
  return current

/-- A stale Markdown file or a rendering failure is a failure of the whole command. -/
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
