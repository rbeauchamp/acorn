/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornSite.Markdown
import AcornSite.Owners
import AcornSite.Reference
import AcornSite.Render

/-! # Site-owned extensions of the documents

`AcornSite.Reference` defines the references a document takes from its Lean owner,
`AcornSite.Owners` the Acorn values the documents splice, `AcornSite.Markdown` the
Markdown rendering kept under `docs/`, and `AcornSite.Render` the check of the built documents.
-/
