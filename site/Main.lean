/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSite.Render
import AcornDocs

/-! # Documentation renderer

Run in Lean's interpreter from `site/` by the site step of verification
(`./scripts/verify.sh site`), after each document has been admitted (`site/Admit.lean`) and
built. It applies `AcornSite.check`, which holds the whole check, to the documents: with no
argument each kept Markdown file must equal the Markdown rendering of its document, and the pages
are then rendered as HTML into `_out`; with `write` the Markdown files are written first.

This is the one file of the site's tooling that imports the documents, and so the modules of the
project that they import; it is elaborated with their declarations in scope. That none of them
can stand in for a part of the check is argued from this file, and no tool checks it:

- The single declaration is an application of `AcornSite.check`, written by its full name with
  no namespace opened, to string literals, a list, tuples and the documents' constants (`%doc`
  names a document's constant and takes its part). Each argument has exactly the type the
  function declares, so elaborating the application asks for no instance and inserts no
  coercion: no instance that a changeable module declares is consulted.
- A second declaration of a name written here cannot be imported beside the first, since Lean
  refuses an import in which one name has two declarations.
- A document admitted by `site/Admit.lean` declares only its document constant and helpers
  whose names no source can write: its forms hold no command that declares an instance or a
  definition.

Keep it to that one application: any other code here would be elaborated with the same
declarations in scope.

It is not a linked executable: linking would compile the native code of every proof
module a document imports, and of the Mathlib modules below them.
-/

/-- Check each ported document against the Markdown file kept for it, then render the manual. -/
def main (args : List String) : IO UInt32 :=
  AcornSite.check
    [("site/AcornDocs/Verification.lean", %doc AcornDocs.Verification, "docs/verification.md")]
    (%doc AcornDocs) args
