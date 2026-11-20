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
reads it from the compiled environment through `read`, the one way a tool executes a project
definition from outside the owner's paths.

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
(`IO.RealWorld`; `runST` takes only an action that works for every token); `validate` refuses a
listed subject whose type names an action type. Trusted and not established here: that those
lists are complete for the pinned Lean, and that Lean's library gives safe code no other way to
run an action.

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
  -- registry of names from outside the project with its membership test.
  `Acorn.Host.Viewer.browserSchema, `Acorn.Host.Viewer.TelemetryShape,
  `Acorn.Host.Viewer.browserRules, `Acorn.Host.Viewer.browserControlRules,
  `Acorn.Host.Viewer.BrowserRule, `AcornDocument.external,
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

/-- Every listed subject is declared, in a project module, with a type that names no effect. A
missing subject is refused, so the list cannot keep an entry for a definition that is gone. -/
def validate (env : Environment) : IO Unit := do
  for subject in subjects do
    let some info := env.find? subject
      | throw (IO.userError s!"subjects: {subject} is listed and not declared")
    unless (home env subject).any AcornModuleInventory.libraryModule do
      throw (IO.userError s!"subjects: {subject} is declared outside the project")
    if let some effect := info.type.getUsedConstants.find? effects.contains then
      throw (IO.userError s!"subjects: the type of {subject} names the effect {effect}")

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

/-- The value of `term`, a Lean term of the type `type`, in the environment of the finished
build. Both are elaborated; a message of the elaborator, an unresolved part or a project
declaration outside the tools that is no listed subject (`admit`) refuses the reading before
anything is evaluated. Unsafe because Lean cannot check that `α` is the type that `type` spells:
each caller writes the two side by side. -/
unsafe def read (α : Type) (env : Environment) (type term : String) : IO α := do
  let parse (text : String) : IO Syntax :=
    IO.ofExcept (Parser.runParserCategory env `term text "<subject>")
  let typeSyntax ← parse type
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
