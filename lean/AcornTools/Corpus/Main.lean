/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.Corpus.Audit

/-- Admit maintained source, with a document-only mode for focused editing. -/
unsafe def main (args : List String) : IO UInt32 := do
  try
    unless args.isEmpty || args == ["documents"] do
      throw (IO.userError "usage: corpus-audit [documents]")
    AcornCorpus.check (args == ["documents"])
    return 0
  catch error =>
    IO.eprintln s!"corpus-audit: {error}"
    return 1
