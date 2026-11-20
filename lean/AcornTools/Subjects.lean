/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean
import AcornTools.ModuleInventory

/-!
# Subjects of the gate's checks

A gate tool judges with its own definitions, which lie under the owner's paths
(`.github/CODEOWNERS`), and imports no project module from outside them: the boundary audit
refuses such an import before anything but the gate program and itself is built
(`AcornBoundaryAudit.toolImports`). Some checks
are statements about a definition of the project itself: a table in a document must equal the
viewer's constants, a published audit command must be one the program's own option parser admits.
Such a definition is a *subject* of the check. It stays where any change may edit it, and a tool
reads it from the compiled environment through `read`, the route by which the tools read every
subject. Where a check's verdict is a test of membership or a comparison, the test is the tool's
and only the data it is applied to is a subject. What holds a tool to this route is that the
tools are themselves under the owner's paths: a tool that evaluated a definition of the change
another way would be a change to an owner path. No check scans the tools for it.

`subjects` is the closed list of those definitions: the list of what a tool may evaluate by
name. `read` elaborates a term a tool writes, in
the environment of the finished build, and evaluates it only when every project declaration from
outside the owner's paths that the elaborated term names is a listed subject. A name of the
project that would stand in for one of Lean's own or one of the tool's, such as an instance the
elaborator selects or a declaration in a namespace that shadows the one written, is therefore
refused: it is no listed subject.

**The evaluation.** `read` adds the elaborated term to the loaded environment as a definition,
Lean's compiler translates it and Lean's interpreter runs it (`Lean.Meta.evalExpr`), with the
compiled code each module's file stores for the subject and for every definition it calls, which
are not listed. No project module is linked into a tool, so no native initializer of the
subject's module exists in the process.

**Why it acts on nothing outside the tool.** For a subject or something it calls to act, it would
have to be an unsafe definition, have a native replacement, run an action, or be code that runs
when a module is compiled or loaded. Source admission refuses `unsafe`, `partial`,
`implemented_by`, `extern`, `csimp`, `initialize` and every macro, elaborator and evaluating
command in each project source, and admits five attributes, none of them a replacement; Lean
refuses a safe definition that names an unsafe one; the theorem inventory refuses a project
declaration that carries a replacement. An action is a function of a state token, and the token
of the real world has an opaque type that no compiled safe definition can inhabit
(`IO.RealWorld`; `runST` takes only an action that works for every token); `admitType` refuses a
listed subject whose type names an action type. Trusted and not established here: that those
lists are complete for the pinned Lean, and that Lean's library gives safe code no other way to
run an action.

**Before a term is elaborated.** Elaborating a call fills an argument its function declares as
filled in when omitted: Lean runs the tactic block the declaration names for it (`autoParam`) or
inserts its default value (`optParam`), before `admit` has seen the elaborated term. `admitType`
therefore refuses a listed subject, or a constructor of a listed inductive type, whose type names
either, and `read` applies it to every listed subject the environment declares before it parses
or elaborates anything.

**What remains, accepted.** The evaluation can fail to end or stop the tool, and a safe
definition can call the runtime's panic and debugging primitives, which write to standard error
or wait. Neither turns a failing check into a pass: a tool that stops or outlasts the deadline
fails its check, and no check reads standard error. A new subject is admitted against this
argument: it holds for a definition of a module that source admission covers whose type is
data.

Adding a subject is a change to this module, which is the owner's to admit.
-/

namespace AcornSubjects
open Lean Meta Elab

/-- The definitions of the project, outside the owner's paths, that a gate check is a statement
about, each with the check that reads it. A listed inductive type admits its constructors and the
eliminators Lean generates for it. -/
def subjects : Array Name := #[
  -- The document audit: the names a document may cite from the viewer's protocol, and the
  -- registry of names from outside the project. Membership in it is the audit's own test.
  `Acorn.Host.Viewer.browserSchema, `Acorn.Host.Viewer.TelemetryShape,
  `Acorn.Host.Viewer.browserRules, `Acorn.Host.Viewer.browserControlRules,
  `Acorn.Host.Viewer.BrowserRule, `AcornDocument.externalSymbols,
  -- The browser audit: the constants a document's table must equal, and the text of the generated
  -- kernel that the kept file must equal.
  `Acorn.Host.Viewer.BrowserConstant, `Acorn.Host.Viewer.BrowserConstant.all,
  `Acorn.Host.Viewer.BrowserConstant.name, `Acorn.Host.Viewer.BrowserConstant.value,
  `Acorn.Host.Viewer.replayCapacity, `Acorn.Host.Viewer.failureLimit,
  `Acorn.Host.Viewer.healthyRunMs, `Acorn.Host.Viewer.mapSideCapacity,
  `Acorn.Host.Viewer.browserKernelJavascript,
  -- The pin audit: the audit arms with their pinned receipts, the two forms the program prints a
  -- word in, and the program's own parser of audit options with its error type.
  `NativeApp.AuditArm, `NativeApp.AuditArm.receipt, `NativeApp.AuditReceipt,
  `NativeApp.AuditReceipt.digest, `NativeApp.AuditReceipt.checksum, `NativeApp.auditWord,
  `NativeApp.hexWord, `NativeApp.auditOptions, `Acorn.Host.Cli.Error]

/-- The types whose presence in a subject's type would make its evaluation an action. -/
def effects : Array Name := #[`IO, `BaseIO, `EIO, `ST, `EST, `IO.RealWorld]

/-- The marks of an argument that Lean's elaborator fills in when a call omits it: by running a
tactic block the declaration names, or with a default value. -/
def filled : Array Name := #[`autoParam, `optParam]

/-- Refuse a listed subject whose type, or the type of a constructor it admits, names an effect
or an argument the elaborator fills in. -/
def admitType (env : Environment) (info : ConstantInfo) : IO Unit := do
  let constructors := match info with
    | .inductInfo declaration => declaration.ctors.filterMap env.find?
    | _ => []
  let refused := effects ++ filled
  for declaration in info :: constructors do
    if let some named := declaration.type.getUsedConstants.find? refused.contains then
      throw (IO.userError s!"subjects: the type of {declaration.name} names {named}")

/-- Whether a declaration of the environment is a listed subject, or a constructor or a generated
eliminator (`rec`, `casesOn`, `recOn`, `ctorIdx`) of a listed inductive type. -/
def listed (env : Environment) (name : Name) : Bool :=
  subjects.contains name ||
    match env.find? name with
    | some (.ctorInfo constructor) => subjects.contains constructor.induct
    | some (.recInfo recursor) => recursor.all.all subjects.contains
    | some _ =>
      match name with
      | .str type field =>
        subjects.contains type && (env.find? type matches some (.inductInfo _)) &&
          (isAuxRecursor env name || field == "ctorIdx")
      | _ => false
    | none => false

/-- The module that declares a constant of the environment, when a module does. -/
def home (env : Environment) (name : Name) : Option Name :=
  (env.getModuleIdxFor? name).bind fun index => env.header.moduleNames[index.toNat]?

/-- Every listed subject is declared, in a project module, with a type that `admitType` admits:
it names no effect and no argument the elaborator fills in. A missing subject is refused, so the
list cannot keep an entry for a definition that is gone. -/
def validate (env : Environment) : IO Unit := do
  for subject in subjects do
    let some info := env.find? subject
      | throw (IO.userError s!"subjects: {subject} is listed and not declared")
    unless (home env subject).any AcornModuleInventory.libraryModule do
      throw (IO.userError s!"subjects: {subject} is declared outside the project")
    admitType env info

/-- Refuse a project declaration, outside the gate's tools, that an elaborated term names and
that is no listed subject. `original` is the environment of the build and `current` the
environment after the term's elaboration, which may have added auxiliary declarations; those are
followed into their own types and values. -/
partial def admit (original current : Environment) (seen : IO.Ref NameSet) (term : Expr) :
    IO Unit := do
  for name in term.getUsedConstants do
    if (← seen.get).contains name then continue
    seen.modify (·.insert name)
    match home original name with
    | some module =>
      if AcornModuleInventory.libraryModule module && !listed original name then
        throw (IO.userError
          s!"subjects: {name} of {module} is no listed subject of a gate check")
    | none =>
      let some info := current.find? name
        | throw (IO.userError s!"subjects: {name} is not declared")
      admit original current seen info.type
      if let some value := info.value? then admit original current seen value

/-- A type a tool may read a subject at, with its spelling as a Lean term. The instances below
are the whole of it: text, numbers, and lists, pairs, options and functions of those. A caller of `read` names the Lean type alone, and the term it reads is elaborated against
the spelling this class gives for that type, so the two cannot disagree at a call. -/
class Readable (α : Type) where
  /-- The type, as a Lean term. -/
  spelling : String

instance : Readable String := ⟨"String"⟩
instance : Readable Nat := ⟨"Nat"⟩
instance {α : Type} [Readable α] : Readable (List α) := ⟨s!"(List {Readable.spelling α})"⟩
instance {α : Type} [Readable α] : Readable (Option α) := ⟨s!"(Option {Readable.spelling α})"⟩
instance {α β : Type} [Readable α] [Readable β] : Readable (α × β) :=
  ⟨s!"({Readable.spelling α} × {Readable.spelling β})"⟩
instance {α β : Type} [Readable α] [Readable β] : Readable (α → β) :=
  ⟨s!"({Readable.spelling α} → {Readable.spelling β})"⟩

/-- The value of `term`, a Lean term of the type `α`, in the environment of the finished build.
Before anything is parsed or elaborated, every listed subject that `env` declares is held to
`admitType`, so elaborating the term runs no tactic block and inserts no default value that a
listed subject declares. A listed subject that `env` does not declare is skipped here, since the
write of the kept browser kernel loads one module alone; `validate` refuses a missing one. The
term is then elaborated against the spelling of `α` (`Readable`); a message of the elaborator, an
unresolved part or a project declaration outside the tools that is no listed subject (`admit`)
refuses the reading before anything is evaluated. Unsafe because the evaluation trusts that each
instance of `Readable` spells its own type, which the six instances above do. -/
unsafe def read (α : Type) [Readable α] (env : Environment) (term : String) : IO α := do
  for subject in subjects do
    if let some info := env.find? subject then admitType env info
  let parse (text : String) : IO Syntax :=
    IO.ofExcept (Parser.runParserCategory env `term text "<subject>")
  let typeSyntax ← parse (Readable.spelling α)
  let termSyntax ← parse term
  let action : MetaM α := do
    let (expected, value) ← Term.TermElabM.run' do
      let expected ← instantiateMVars (← Term.elabType typeSyntax)
      let value ← Term.elabTermEnsuringType termSyntax expected
      Term.synthesizeSyntheticMVarsNoPostponing
      pure (expected, ← instantiateMVars value)
    let log ← Core.getMessageLog
    if log.hasErrors then
      throwError "subjects: {term}: {← log.toList.mapM (·.toString)}"
    if expected.hasMVar || value.hasMVar then
      throwError "subjects: {term}: the term or its type is not fully determined"
    let seen ← IO.mkRef ({} : NameSet)
    admit env (← getEnv) seen expected
    admit env (← getEnv) seen value
    Meta.evalExpr α expected value
  let (result, _, _) ← action.toIO { fileName := "<subject>", fileMap := default } { env }
  return result

end AcornSubjects
