/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornTools.Boundary.Audit

/-! # Command admission inside Lean's compiler

Lake loads this module as a plugin when compiling a governed module. In Lean v4.35.0
`importModules` initializes plugins before constructing the environment extensions.
The command category therefore uses this parser in the module's own evolving environment.
-/
namespace AcornBoundaryAudit
open Lean Parser

/-- Keep the pinned parser for each category. For a command, return its tree to Lean
only after the same inspection used by source admission. Lean also elaborates partial
trees when recovering from a parse error, so a refusal replaces the entire result.
The category parser's stack has one result above its inaccessible prefix
(`Lean.Parser.withCacheFn`). -/
private def admittedParser (parse : CategoryParserFn) : CategoryParserFn := fun category =>
  if category != `command then parse category else fun context state =>
    let parsed := parse category context state
    let owner := context.env.mainModule
    match inspectCommand owner parsed.stxStack.back with
    | .ok () => parsed
    | .error reason => parsed.popSyntax.mkUnexpectedError s!"Lean boundary {owner}: {reason}"

initialize
  categoryParserFnRef.modify admittedParser

end AcornBoundaryAudit
