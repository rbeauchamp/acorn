/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import VersoManual

/-! # References a document takes from its Lean owner

A document names Lean declarations, modules, statements and values. Each form here makes
that reference part of the document's elaboration, so a reference that no longer matches its
owner fails the build of the page, and Lake rebuilds the page when an owner it imports
changes.

- `{decl}` and `{leanModule}` take a name as written and require it to resolve.
- `{splice}` and `{spliceCode}` take a Lean term of type `String`. The term itself becomes
  part of the document, so the text shown is the owner's value when the page is rendered;
  the document holds no copy of it.
- A `spliced` code block does the same for a whole block.
- `{statement}` prints a theorem's statement from the environment the document elaborates
  in.

Verso and Lean's elaborator are the trusted tools here. A reference is checked for
existence, type and current value; that the surrounding prose describes the owner
faithfully remains a matter for review.
-/

open Lean Elab
open Verso ArgParse Doc Elab Genre.Manual
open Verso.Output (Html)

namespace AcornSite

/- A code block with an optional language: the text is shown verbatim. -/
block_extension Block.fenced (language shown : String) where
  data := Json.arr #[.str language, .str shown]
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[.str language, .str shown] := data
        | Verso.reportError s!"Expected a language and a text, got {data}"; pure .empty
      return {{<pre><code class={{"language-" ++ language}}>{{shown}}</code></pre>}}

/-- `{decl}` names a declaration by its full name; the name must resolve to itself. -/
@[role]
def decl : RoleExpanderOf Unit
  | (), inlines => do
    let code ← oneCodeStr inlines
    let written := code.getString.toName
    let resolved ← realizeGlobalConstNoOverloadWithInfo (mkIdentFrom code written)
    unless resolved == written do
      throwErrorAt code "write the full name {resolved}"
    ``(Verso.Doc.Inline.code $(quote code.getString))

/-- `{leanModule}` names a module the document imports, directly or through another module.
The import is what makes Lake rebuild the page when the module changes. -/
@[role]
def leanModule : RoleExpanderOf Unit
  | (), inlines => do
    let code ← oneCodeStr inlines
    let written := code.getString.toName
    unless written.toString == code.getString && ((← getEnv).getModuleIdx? written).isSome do
      throwErrorAt code "{code.getString} is not a module this document imports"
    ``(Verso.Doc.Inline.code $(quote code.getString))

/-- `{splice}` shows the value of a Lean term of type `String` as ordinary text. -/
@[role]
def splice : RoleExpanderOf Unit
  | (), inlines => do
    let term : Term := ⟨← SyntaxUtils.parseStrLitAsCategory `term (← oneCodeStr inlines)⟩
    ``(Verso.Doc.Inline.text ($term : String))

/-- `{spliceCode}` shows the value of a Lean term of type `String` as code. -/
@[role]
def spliceCode : RoleExpanderOf Unit
  | (), inlines => do
    let term : Term := ⟨← SyntaxUtils.parseStrLitAsCategory `term (← oneCodeStr inlines)⟩
    ``(Verso.Doc.Inline.code ($term : String))

/-- A `sh` block: shell text shown verbatim. -/
@[code_block]
def sh : CodeBlockExpanderOf Unit
  | (), text => ``(Verso.Doc.Block.other (Block.fenced "sh" $(quote text.getString)) #[])

/-- The language a `spliced` block is shown in. -/
structure SplicedArgs where
  /-- The language name of the rendered block. -/
  language : Ident

instance : FromArgs SplicedArgs DocElabM where
  fromArgs := SplicedArgs.mk <$> .positional `language .ident

/-- A `spliced` block holds a Lean term of type `String`; the block shows the term's value
in the given language. -/
@[code_block]
def spliced : CodeBlockExpanderOf SplicedArgs
  | { language }, text => do
    let term : Term := ⟨← SyntaxUtils.parseStrLitAsCategory `term text⟩
    ``(Verso.Doc.Block.other (Block.fenced $(quote language.getId.toString) ($term : String)) #[])

/-- The theorem a `{statement}` block prints. -/
structure StatementArgs where
  /-- The theorem's full name. -/
  name : Ident

instance : FromArgs StatementArgs DocElabM where
  fromArgs := StatementArgs.mk <$> .positional `name .ident

/-- `{statement Name}` prints the statement of the theorem `Name` as Lean checked it. -/
@[block_command]
def statement : BlockCommandOf StatementArgs
  | { name } => do
    let resolved ← realizeGlobalConstNoOverloadWithInfo name
    unless resolved == name.getId do
      throwErrorAt name "write the full name {resolved}"
    unless (← getConstInfo resolved) matches .thmInfo _ do
      throwErrorAt name "{resolved} is not a theorem"
    let signature ← PrettyPrinter.ppSignature resolved
    let text := "theorem " ++ signature.fmt.pretty 100 ++ "\n"
    ``(Verso.Doc.Block.other (Block.fenced "lean" $(quote text)) #[])

end AcornSite
