/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.Corpus.Audit

/-! # `corpus-audit` executable

Command-line entry point of the maintained-source corpus audit. With no argument
it runs `AcornCorpus.check` over all maintained source; with `documents` it
checks documents only; with `browser-kernel write` it writes the kept browser kernel from its
Lean emitter, read from the build of that emitter's module. Any refusal is printed on standard
error with exit status 1.
-/

/-- Admit maintained source, with a document-only mode for focused editing. -/
unsafe def main (args : List String) : IO UInt32 := do
  try
    if args == ["browser-kernel", "write"] then
      -- Only the emitter's module is loaded, so the whole list of subjects is not validated
      -- here as the audit does; the reading still refuses a declaration that is not listed.
      let env ← AcornDocument.environment #[`Acorn.Host.Viewer.BrowserKernel]
      AcornBrowserAudit.kernel env (write := true)
      return 0
    unless args.isEmpty || args == ["documents"] do
      throw (IO.userError "usage: corpus-audit [documents | browser-kernel write]")
    AcornCorpus.check (args == ["documents"])
    return 0
  catch error =>
    IO.eprintln s!"corpus-audit: {error}"
    return 1
