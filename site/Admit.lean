/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean
import Verso.SyntaxUtils
import AcornTools.ModuleInventory

/-! # Admission of a document before it is elaborated

A document under `site/AcornDocs` is a Lean file that any change may edit, and elaborating it
runs whatever its commands call. The site step of verification therefore runs this program on
each document, in Lean's interpreter from `site/`, before Lake builds the document
(`AcornGate.site`). It reads the file as Lean itself does: the header with Lean's header parser,
then one command at a time with the parser of the environment so far, which after `#doc` is
Verso's own block parser, so what is inspected is exactly what the build will elaborate. Each
command is inspected first and elaborated only when it is admitted; the first one that is not
ends the run with a refusal, before it has been elaborated.

**What a document may hold** is the closed list below, which is exactly what Acorn's documents use:

- imports of `VersoManual`, of `AcornSite`, of a module of the Lean package in `lean/`, and, in
  the root document `AcornDocs` alone, of the documents it includes;
- before the text, `open` of the namespaces `openNamespaces`, and `#doc (Manual) "Title" =>`,
  whose title is plain text (`titleCharacter`), since Verso reads a title as text of the document;
- in the text: paragraphs, headings, links to a URL, bold text, inline code, line breaks, and a
  metadata block that sets `tag` to a string;
- the roles `roleNames`: `{decl}` and `{leanModule}` around one code span holding a name,
  `{splice}` and `{spliceCode}` around one code span holding a Lean term;
- the code blocks `sh`, shown verbatim, and `spliced` with one language name, holding a Lean term;
- the block commands `{include n AcornDocs.Module}` and `{statement Name}`.

**A Lean term** in a splice is read by Verso's own reader of a term in a string and may be built
only from the kinds `termKinds`: a name, an application, parentheses, `.name`, a string and an
interpolated string `s!"…"`. It holds no tactic block, no `do`, no anonymous function and no
other notation, so elaborating it runs Lean's elaborator of an application and whatever the
functions it names declare for their own arguments.

Everything else is refused by the name of its syntax kind, a list or an emphasis included: a
document that needs another form needs a change to this list first, and this file lies under the
owner's paths (`.github/CODEOWNERS`), so that change is the owner's to admit. One document is read
per run: Lean keeps state of an import for the life of the process.
-/

open Lean Elab

namespace AcornSiteAdmission

/-- The namespaces a document may open. -/
def openNamespaces : Array Name := #[`Verso.Genre, `Manual, `AcornSite]

/-- The characters a document's title may hold: letters, digits, spaces and four marks of
punctuation. Verso parses a title as text of a document and elaborates each part of it, so a
title holds no character that begins a role, code, a link, emphasis or an escape. -/
def titleCharacter (c : Char) : Bool :=
  c.isAlphanum || c == ' ' || c == ',' || c == '.' || c == '\'' || c == '-'

/-- The roles a document may use. -/
def roleNames : Array Name := #[`decl, `leanModule, `splice, `spliceCode]

/-- The roles whose code span holds a Lean term. -/
def termRoles : Array Name := #[`splice, `spliceCode]

/-- The syntax kinds of a document's commands and of its text. -/
def documentKinds : Array Name := #[nullKind, strLitKind, numLitKind,
  ``Parser.Command.open, ``Parser.Command.openSimple, ``Parser.Command.eoi,
  `Verso.Doc.Concrete.replaceDoc, `Verso.Doc.Concrete.addBlockCmd,
  `Verso.Doc.Concrete.addLastBlockCmd,
  `Lean.Doc.Syntax.para, `Lean.Doc.Syntax.header, `Lean.Doc.Syntax.codeblock,
  `Lean.Doc.Syntax.metadata_block, `Lean.Doc.Syntax.command, `Lean.Doc.Syntax.text,
  `Lean.Doc.Syntax.linebreak, `Lean.Doc.Syntax.code, `Lean.Doc.Syntax.bold,
  `Lean.Doc.Syntax.link, `Lean.Doc.Syntax.url, `Lean.Doc.Syntax.role, `Lean.Doc.Syntax.anon,
  `Lean.Doc.Syntax.arg_ident, `Lean.Doc.Syntax.arg_num]

/-- The syntax kinds of a metadata block's contents: fields set to strings. -/
def metadataKinds : Array Name := #[nullKind, strLitKind, ``Parser.Term.structInstFields,
  ``Parser.Term.structInstField, ``Parser.Term.structInstLVal, ``Parser.Term.structInstFieldDef]

/-- The syntax kinds of a spliced Lean term. -/
def termKinds : Array Name := #[nullKind, strLitKind, hygieneInfoKind,
  ``Parser.Term.app, ``Parser.Term.paren, ``Parser.Term.hygienicLParen, ``Parser.Term.dotIdent,
  `termS!_, interpolatedStrKind, interpolatedStrLitKind]

/-- A refusal names the document and what it holds. -/
def refuse {α : Type} (file reason : String) : IO α :=
  throw (IO.userError s!"{file}: {reason}")

/-- Every node of `syntaxTree` has one of the kinds `allowed`, and no part of it is missing. A
name is a leaf of any tree; the callers say which names each form admits. -/
partial def closed (file what : String) (allowed : Array Name) (syntaxTree : Syntax) : IO Unit :=
  match syntaxTree with
  | .missing => refuse file s!"{what} with a missing part"
  | .atom .. | .ident .. => pure ()
  | .node _ kind arguments => do
    unless allowed.contains kind do refuse file s!"{what} holds the unadmitted form {kind}"
    for argument in arguments do closed file what allowed argument

/-- Every name in `syntaxTree`. -/
partial def names (syntaxTree : Syntax) : Array Name :=
  match syntaxTree with
  | .ident _ _ name _ => #[name]
  | .node _ _ arguments => arguments.flatMap names
  | _ => #[]

/-- The one name an argument list `{… name}` holds in the position `index`, when that argument is
a bare name. -/
def nameArgument (arguments : Syntax) (index : Nat) : Option Name :=
  let argument := arguments[index]
  if argument.isOfKind `Lean.Doc.Syntax.anon && argument[0].isOfKind `Lean.Doc.Syntax.arg_ident
    then some argument[0][0].getId else none

/-- What the elaborated commands so far have left: the environment whose parser reads the next
command, and the reader of a Lean term in a string. -/
structure Reader where
  /-- The document. -/
  file : String
  /-- Verso's own reading of the contents of a string literal as a Lean term, in the current
  environment (`Verso.SyntaxUtils.parseStrLitAsCategory`). -/
  term : StrLit → IO Syntax

/-- The Lean term in the string literal `text` is built from the admitted kinds alone. -/
def Reader.admitTerm (reader : Reader) (text : Syntax) : IO Unit := do
  unless text.isOfKind strLitKind do refuse reader.file "a splice that holds no text"
  closed reader.file "a spliced term" termKinds (← reader.term ⟨text⟩)

/-- Inspect one part of a document's text, and every part inside it. -/
partial def Reader.admit (reader : Reader) (part : Syntax) : IO Unit := do
  if part.isMissing then refuse reader.file "text with a missing part"
  if part.isAtom || part.isIdent then return
  let kind := part.getKind
  unless documentKinds.contains kind do
    refuse reader.file s!"the document holds the unadmitted form {kind}"
  if kind == `Lean.Doc.Syntax.role then
    let role := part[1].getId
    unless roleNames.contains role do refuse reader.file s!"the unadmitted role {role}"
    unless part[2].getNumArgs == 0 do refuse reader.file s!"arguments to the role {role}"
    let #[code] := part[5].getArgs
      | refuse reader.file s!"the role {role} around anything but one code span"
    unless code.isOfKind `Lean.Doc.Syntax.code && code[1].isOfKind strLitKind do
      refuse reader.file s!"the role {role} around anything but one code span"
    let nameText := (code[1].isStrLit?.getD "!").toList.all fun c =>
      c.isAlphanum || c == '.' || c == '_' || c == '\''
    if termRoles.contains role then reader.admitTerm code[1]
    else unless nameText do
      refuse reader.file s!"the role {role} around text that is no name"
  else if kind == `Lean.Doc.Syntax.codeblock then
    let #[name, arguments] := part[1].getArgs
      | refuse reader.file "a code block with no name"
    if name.getId == `sh && arguments.getNumArgs == 0 then pure ()
    else if name.getId == `spliced && arguments.getNumArgs == 1 &&
        (nameArgument arguments 0).isSome then
      reader.admitTerm part[3]
    else refuse reader.file s!"the unadmitted code block {name.getId} {arguments}"
  else if kind == `Lean.Doc.Syntax.command then
    let name := part[1].getId
    let arguments := part[2]
    if name == `include && arguments.getNumArgs == 2 &&
        arguments[0].isOfKind `Lean.Doc.Syntax.anon &&
        arguments[0][0].isOfKind `Lean.Doc.Syntax.arg_num &&
        (nameArgument arguments 1).any (`AcornDocs).isPrefixOf then pure ()
    else if name == `statement && arguments.getNumArgs == 1 &&
        (nameArgument arguments 0).isSome then pure ()
    else refuse reader.file s!"the unadmitted block command {name} {arguments}"
  else if kind == `Lean.Doc.Syntax.metadata_block then
    closed reader.file "a metadata block" metadataKinds part[1]
    unless names part[1] == #[`tag] do
      refuse reader.file "a metadata block that sets anything but `tag`"
  else
    for argument in part.getArgs do reader.admit argument

/-- Inspect one command of a document, before it is elaborated. -/
def Reader.admitCommand (reader : Reader) (command : Syntax) : IO Unit := do
  let kind := command.getKind
  if kind == ``Parser.Command.open then
    closed reader.file "an `open`" documentKinds command
    unless command[1].isOfKind ``Parser.Command.openSimple &&
        (names command).all openNamespaces.contains do
      refuse reader.file s!"an unadmitted `open`: {command}"
  else if kind == `Verso.Doc.Concrete.replaceDoc then
    closed reader.file "the `#doc` line" documentKinds command
    unless command[2].isIdent && command[2].getId == `Manual do
      refuse reader.file "a document of a genre other than `Manual`"
    -- Verso reads the title as text of a document and elaborates what it finds there, so a
    -- title is plain: characters that begin no form of the text.
    unless (command[4].isStrLit?.getD "{").toList.all titleCharacter do
      refuse reader.file "a title that is not plain text"
  else if kind == `Verso.Doc.Concrete.addBlockCmd || kind == `Verso.Doc.Concrete.addLastBlockCmd then
    reader.admit command
  else unless kind == ``Parser.Command.eoi do
    refuse reader.file s!"the unadmitted command {kind}"

/-- A module a document may import: Verso's manual genre, the site's own extensions, a module of
the Lean package in `lean/`, and, for the root document alone, a document it includes. -/
def importAdmitted (document imported : Name) : Bool :=
  imported == `Init || imported == `VersoManual || imported == `AcornSite ||
    AcornModuleInventory.libraryModule imported ||
    AcornModuleInventory.toolingModules.contains imported ||
    (document == `AcornDocs && (`AcornDocs).isPrefixOf imported && imported != `AcornDocs)

/-- Read one document as Lean reads it, inspecting each command before elaborating it. Returns
the number of commands admitted. Unsafe because the imports' initializers run, as in every
elaboration. -/
unsafe def run (file : String) : IO Nat := do
  let path := System.FilePath.mk file
  let document := (path.withExtension "").components.foldl (fun name part => name.str part)
    Name.anonymous
  unless (`AcornDocs).isPrefixOf document && path.extension == some "lean" do
    refuse file "not a document under site/AcornDocs"
  let inputContext := Parser.mkInputContext (← IO.FS.readFile path) file
  let (header, parserStart, messages) ← Parser.parseHeader inputContext
  if messages.hasErrors then refuse file "the header does not parse"
  for imported in headerToImports header do
    unless importAdmitted document imported.module do
      refuse file s!"the unadmitted import {imported.module}"
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let (env, messages) ← processHeader header {} messages inputContext
  let context : Command.Context :=
    { fileName := file, fileMap := inputContext.fileMap, snap? := none, cancelTk? := none }
  let mut state := Command.mkState env messages {}
  let mut parserState := parserStart
  let mut admitted := 0
  repeat
    let scope := state.scopes.head!
    let (command, parserNext, log) := Parser.parseCommand inputContext
      { env := state.env, options := scope.opts, currNamespace := scope.currNamespace,
        openDecls := scope.openDecls } parserState state.messages
    parserState := parserNext
    let current := { state with messages := log }
    let reader : Reader := { file, term := fun text => do
      let read : Command.CommandElabM Syntax :=
        Command.liftCoreM (Verso.SyntaxUtils.parseStrLitAsCategory `term text)
      match ← ((read.run context).run current).toIO' with
      | .ok (term, _) => pure term
      | .error _ => refuse file s!"a spliced term that does not parse: {text}" }
    reader.admitCommand command
    admitted := admitted + 1
    if Parser.isTerminalCommand command then
      state := current
      break
    match ← (((Command.elabCommandTopLevel command).run context).run current).toIO' with
    | .ok (_, next) => state := next
    | .error _ => refuse file "a command whose elaboration was interrupted"
  if state.messages.hasErrors then
    for message in state.messages.toList do IO.eprint (← message.toString)
    refuse file "the document does not elaborate"
  return admitted

end AcornSiteAdmission

/-- Admit one document, named by its path under `site/`. -/
unsafe def main (args : List String) : IO UInt32 := do
  let [file] := args
    | IO.eprintln "usage: lean --run Admit.lean AcornDocs/<document>.lean"
      return 2
  try
    let admitted ← AcornSiteAdmission.run file
    IO.println s!"site: {file}: {admitted} commands, each admitted before it was elaborated"
    return 0
  catch error =>
    IO.eprintln s!"site: {error}"
    return 1
