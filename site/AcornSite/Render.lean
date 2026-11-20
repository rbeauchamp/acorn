/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import VersoManual
import AcornSite.Markdown

/-! # The documents' check

`check` is the whole of what the site step of verification decides once the documents are
built: each kept Markdown file equals the Markdown rendering of its document, and Verso renders
the pages as HTML, which fails on an unresolved cross-reference. With `write` it writes the
Markdown files first. Nothing is published.

It is defined here and not in `site/Main.lean` because this module imports no document and no
module of the project that a document imports: its imports are Verso, which a document imports
as well, and the site's Markdown rendering. The boundary audit requires of every module of the
site's own tooling that it import no document and no project module from outside the owner's
paths (`AcornBoundaryAudit.toolImports`). Its code is therefore elaborated with no declaration
of the project's changeable modules in scope, and none can be what a comparison or an instance
here resolves to. `Main.lean` only applies `check` to the documents.
-/

open Verso.Genre Manual

namespace AcornSite

/-- Write, or compare with, the kept Markdown rendering of each ported document: its Verso
source, its elaborated value and the Markdown file kept for readers of the repository, with
paths relative to the repository root. -/
def markdown (pages : List (String × Verso.Doc.Part Manual × String)) (write : Bool) :
    IO Bool := do
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

/-- The site's check of the ported documents `pages` and of the whole manual `root`, run from
`site/`. A stale Markdown file or a rendering failure is a failure of the whole command. -/
def check (pages : List (String × Verso.Doc.Part Manual × String))
    (root : Verso.Doc.Part Manual) (args : List String) : IO UInt32 := do
  let write ← match args with
    | [] => pure false
    | ["write"] => pure true
    | _ =>
      IO.eprintln "usage: lean --run Main.lean [write]"
      return 1
  unless ← markdown pages write do return 1
  manualMain root (options := []) (config := {
    emitTeX := false, emitHtmlSingle := .no, emitHtmlMulti := .immediately, htmlDepth := 1,
    sourceLink := some "https://github.com/rbeauchamp/acorn",
    issueLink := some "https://github.com/rbeauchamp/acorn/issues" })

end AcornSite
