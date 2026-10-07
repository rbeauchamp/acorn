/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean
import Regula.Contract

/-!
# Decision inventory

A definition is verdict-shaped when its result type, after its arguments, is `Bool`,
`Option`, `Except` or `Decidable`. Every verdict-shaped definition of the claimed libraries
is in exactly one of three classes.

* It is structural: a structure field, which is stored data, or a function with a
  `Decidable` result, which carries both directions of its decision in its type.
* It is the implementation of a `Regula.ExecutableContract` that a decision registry states
  (`Acorn.Decisions` or `AcornVerif.Decisions`).
* It is an entry of `excluded`, with the shape of its type and the reason it carries no
  contract.

A contract has one of two strengths, and the audit prints how many implementations have each.
A contract whose statement is a decision kind (`Regula.Decides`, `Regula.DecidesSoundly`,
`Regula.DecidesCompletely`) carries a witness of each outcome it claims, and the Regula audit
checks that its specification does not name the implementation. A contract with any other
statement is a requirement that the Regula audit does not check for witnesses or
independence: that audit checks only that the theorem is proved about the executing
definition.

The ownership audit reads the classes of each definition from the compiled environment and
applies `classified`, the decision of this inventory. A definition in no class or in two
fails verification. Every entry of `excluded` is validated on its own as well: it names
exactly one verdict-shaped definition, which has no other entry, no contract and is not
structural; it states the shape the audit computes; and its reason is supported by the
facts the audit computes (`Reason.supported`). A new verdict-shaped definition therefore
cannot arrive unlisted, and a contract cannot be removed without an entry here.

## What is computed

The domain, the three classes, the shape and every reason are computed from the compiled
environment. `Reason` states the fact behind each reason, and which part of that fact is a
relationship that the environment records and which part is a position; an entry whose fact
is false fails verification.

The reasons `unproved`, `composed` and `proposal` include the fact that no written theorem
names the definition. The reasons `derived`, `default` and `model` are other facts and do not
include it: a written theorem can name such a definition, and the audit prints, for each
reason, how many of its entries a written theorem names. The reason `named` is for a
definition that a written theorem does name and that has no contract: the entry gives one
such theorem, and the audit checks it.

The audit computes, for every excluded definition, whether the implementation of a registered
decision reaches it through definition bodies (`reachable`). A definition that a written
theorem names and a registered decision reaches is refused: it needs a contract. A definition
that no written theorem names and a registered decision reaches is in the list `relied`; it
has no contract of its own, and the contract of the decision that reaches it is the evidence.
The reach of every entry must agree with that list (`Evidence.placed`), and `relied_count`
states its size, so the list cannot grow without a change of that theorem. The inventory
makes no statement about what a caller does with the result of an excluded definition.
`named_count` states how many entries the reason `named` has.

## The domain

The domain holds every constant of the surveyed modules that can carry an executable body, a
definition or an opaque constant, private ones included, whose type is verdict-shaped by the
one telescope of this module (`signatureOf`). A field default and an instance are such
constants. A constant leaves the domain only as a recursion companion of a parent declaration
(`companion?`): the parent has equation data of a recursion compiler in the environment, the
name is the one that compiler derives from the parent, and the companion has the parent's
signature or is applied by the parent's body. A flag, a name or a position alone removes
nothing. A matcher, an auxiliary recursor and a no-confusion definition return a value of
their motive or a sort, so they are not verdict-shaped and need no rule. The audit prints how
many constants left as each kind of companion. `controls` checks written declarations that a
name, a flag or a count of written binders would decide wrongly.

## Witnesses

A witness refuses a constant function: a contract with an accepted input is false of a
function that refuses every input, and a contract with a refused input is false of a function
that accepts every input. Each decision function with a contract has both, or a proof that
the one that is missing does not exist. The audit refuses a function with neither.

A two-way kind about the function that its condition binds (`kindAbout`) counts for both
sides. Its type states that the function accepts exactly the inputs that satisfy the
specification (`Regula.Decides.iff`), so it fixes the verdict at every input, and it states
that both outcomes occur. Its type names no input: the input of a witness is inside a proof,
which the kernel does not tell from any other proof of the same proposition. A one-way kind
fixes one direction only, so it does not count as a witness here. Each other witness is a
marked fact (`acceptanceMarkers`, `refusalMarkers`) at the top level of a condition, with a
standard acceptance predicate, about the function that the condition binds (`witnessInputs`).
Such a fact is below no quantifier and no hypothesis, and it names its input.

The audit examines the input of every marked fact with one function (`reaches`), and it
counts the fact only when the input does not depend on the decision function. The dependency
relation is the one of the kernel (`dependencies`): a constant depends on the constants of its
type, on the constants of its value when it has one (a definition, a theorem and an opaque
constant have one), and on the parts of its inductive declaration. `dependencies` matches on
every constructor of `ConstantInfo`, so no kind of constant is left unread. The walk stays
inside the libraries of this repository (`own`), because no other library imports them. A
constant of these libraries that the walk cannot find counts as a dependency on the function.
The audit reads the dependencies of the constants that a witness input reaches (`closure`).

An obstruction has one kind, and the audit accepts no other: a proved obstruction
(`noAcceptedMarkers`, `noRefusedMarkers`) carries a proposition that states the opposite fact
for every input of the function (`everyInput`), so the absence of the input is proved. No
text and no limit of an evaluator stands in the place of a missing input.

## Forms

The audit prints the form of each part of each statement with no kind (`Form`, `formsOf`).
It infers nothing. A part has a strong form only when it has one of two exact shapes: it
quantifies over exactly the inputs of the function, and its body is an equivalence between an
equation about the result at those inputs and a proposition that does not name the function
(`verdict`), or it is such an equation alone (`result`). Each other part that names the
function outside a marker is `unclassified`. That word says nothing about the strength of the
part: the theorem behind it can be exact, one-way or conditional. The witnesses, and not the
form, are what refuse a constant function.

This is a check that every such definition has been classified and that each computed fact
holds. Whether a contract states the intended specification is review.
-/
namespace AcornDecisionInventory
open Lean Meta

/-- Whether a type of a definition depends on one of its arguments. A decision kind is stated
about a function between two fixed types. -/
inductive Shape where
  /-- No argument type and no result type names an argument of the definition. -/
  | fixed
  /-- An argument type or the result type names an argument of the definition. -/
  | dependent
  deriving DecidableEq, Repr

/-- Why a verdict-shaped definition carries no contract. Each reason is a fact that the audit
computes, and an entry whose fact is false fails verification. The docstring of each reason
says which part of its fact comes from a relationship that the environment records and which
part is a position. -/
inductive Reason where
  /-- No written theorem of the maintained libraries names the definition in its statement.
  This is the absence of a direct reference and nothing more: a theorem about a caller can
  still imply a property of the definition. A contract of a decision registry is not counted.
  A theorem is not written when the environment relates it to a parent declaration: a proof
  field of a structure, a reserved equation name, or the injectivity or size theorem that
  Lean names for a recorded constructor. -/
  | unproved
  /-- The fact of `unproved`, and the body applies a definition that has a contract or a
  `Decidable` result. The contracts of the decisions it applies stand. -/
  | composed
  /-- The fact of `unproved`; the definition belongs to the certificate search module; and
  each definition outside that module whose body names it also applies a definition with a
  contract or a `Decidable` result. The module is a position. The caller fact is computed
  from the bodies. It does not show that the caller passes the proposal to that decision. -/
  | proposal
  /-- The definition is the `beq` of a registered instance of `BEq` for a type of the same
  module, and the recorded ranges of the definition and of the instance lie inside the
  declaration of that type, where a `deriving` clause puts what it generates. The instance
  and the type are recorded relationships. That the comparison is generated is inferred from
  the ranges, which are a position: Lean records no relation between a `deriving` clause and
  what it generates. A macro that expands to a type and a handwritten instance with the
  derived names would be classed wrongly as derived. A `deriving instance` command that
  stands apart from its type is classed as not derived, which fails closed. -/
  | derived
  /-- The definition is the default value of a structure field that is not a function, so it
  is a stored value: the field is a recorded projection, the name is the one Lean derives for
  its default, and the projection has no argument beyond the structure. -/
  | default
  /-- The definition belongs to a module of the proof library. The library is a position. No
  executable runs the definition as long as the boundary audit refuses an import of the proof
  library by an executing module; this inventory does not check that itself. A definition of
  the proof library that an executable imported would be classed wrongly. -/
  | model
  /-- A written theorem of a maintained module names the definition in its statement, and
  `standing` is one such theorem; no contract states the definition; and no implementation of
  a registered decision reaches the definition through definition bodies. The fact says
  nothing about what a caller does with the result. -/
  | named (standing : Name)
  deriving DecidableEq, Repr

/-- The standing theorem of an entry that a theorem names. -/
def Reason.standing? : Reason → Option Name
  | .named standing => some standing
  | _ => none

/-- The name of a reason, without its standing theorem. -/
def Reason.label : Reason → String
  | .unproved => "unproved" | .composed => "composed" | .proposal => "proposal"
  | .derived => "derived" | .default => "default" | .model => "model"
  | .named _ => "named"

/-- The names of the reasons with no standing theorem. -/
def Reason.plainLabels : List String :=
  ["unproved", "composed", "proposal", "derived", "default", "model"]

/-- The name of the reason with a standing theorem. -/
def Reason.namedLabel : String := "named"

/-- The list and the label hold every reason, each for what it is. -/
theorem Reason.label_listed (reason : Reason) :
    (reason.standing?.isNone → reason.label ∈ Reason.plainLabels) ∧
      (reason.standing?.isSome → reason.label = Reason.namedLabel) := by
  cases reason <;> simp [Reason.label, Reason.standing?, Reason.plainLabels, Reason.namedLabel]

/-- The facts the audit computes about one excluded definition. -/
structure Evidence where
  /-- A written theorem of the maintained libraries, outside the decision registries,
  mentions the definition in its statement. -/
  mentioned : Bool
  /-- The body applies a definition that has a contract or a `Decidable` result. -/
  applies : Bool
  /-- The definition belongs to the certificate search module, and each outside definition
  that names it applies a definition with a contract or a `Decidable` result. -/
  searching : Bool
  /-- The definition is the comparison of a derived instance. -/
  generated : Bool
  /-- The definition is the default of a structure field that is not a function. -/
  fieldDefault : Bool
  /-- The definition belongs to the proof library. -/
  proofLibrary : Bool
  /-- The entry's standing theorem is such a written theorem and mentions the definition. -/
  standing : Bool
  /-- The implementation of a registered decision reaches the definition. -/
  reached : Bool
  /-- The definition is in the list `relied`. -/
  relied : Bool
  deriving DecidableEq, Repr

/-- The reach of an entry agrees with the list `relied`: a definition that a registered
decision reaches is in the list, a definition in the list is reached, and no written theorem
names a definition in the list. -/
def Evidence.placed (evidence : Evidence) : Bool :=
  evidence.reached == evidence.relied && !(evidence.relied && evidence.mentioned)

/-- Whether the computed facts support a reason. -/
def Reason.supported : Reason → Evidence → Bool
  | .unproved, evidence => !evidence.mentioned && evidence.placed
  | .composed, evidence => !evidence.mentioned && evidence.applies && evidence.placed
  | .proposal, evidence => !evidence.mentioned && evidence.searching && evidence.placed
  | .derived, evidence => evidence.generated && evidence.placed
  | .default, evidence => evidence.fieldDefault && evidence.placed
  | .model, evidence => evidence.proofLibrary && evidence.placed
  | .named _, evidence => evidence.standing && !evidence.reached && !evidence.relied

/-- A reason with no standing theorem does not depend on a standing theorem. -/
theorem Reason.supported_plain (reason : Reason) (left right : Evidence)
    (plain : reason.standing? = none) (mentioned : left.mentioned = right.mentioned)
    (applies : left.applies = right.applies) (searching : left.searching = right.searching)
    (generated : left.generated = right.generated)
    (fieldDefault : left.fieldDefault = right.fieldDefault)
    (proofLibrary : left.proofLibrary = right.proofLibrary)
    (reached : left.reached = right.reached) (relied : left.relied = right.relied) :
    reason.supported left = reason.supported right := by
  cases reason <;> simp_all [Reason.supported, Reason.standing?, Evidence.placed]

/-- A "no theorem" reason is refused for a definition that a theorem mentions. -/
theorem Reason.unproved_refused (reason : Reason) (evidence : Evidence)
    (mentioned : evidence.mentioned = true)
    (unproved : reason = .unproved ∨ reason = .composed ∨ reason = .proposal) :
    reason.supported evidence = false := by
  rcases unproved with rfl | rfl | rfl <;> simp [Reason.supported, mentioned]

/-- An entry that a theorem names is supported exactly when its standing theorem is checked,
no registered decision reaches the definition and the definition is not in `relied`. -/
theorem Reason.supported_named (reason : Reason) (evidence : Evidence) (standing : Name)
    (named : reason.standing? = some standing) :
    reason.supported evidence = (evidence.standing && !evidence.reached && !evidence.relied) := by
  cases reason <;> simp_all [Reason.supported, Reason.standing?]

/-- For every reason, a definition that a registered decision reaches and that is not in
`relied` is refused: it needs a contract or a place in that list. -/
theorem Reason.reached_refused (reason : Reason) (evidence : Evidence)
    (reached : evidence.reached = true) (unlisted : evidence.relied = false) :
    reason.supported evidence = false := by
  cases reason <;> simp [Reason.supported, Evidence.placed, reached, unlisted]

/-- For every reason, a definition in `relied` that a written theorem names is refused: a
definition that a theorem names and a registered decision reaches needs a contract. -/
theorem Reason.relied_refused (reason : Reason) (evidence : Evidence)
    (relied : evidence.relied = true) (mentioned : evidence.mentioned = true) :
    reason.supported evidence = false := by
  cases reason <;> simp [Reason.supported, Evidence.placed, relied, mentioned]

/-- The decision registries: the modules whose contracts count toward the inventory. -/
def registries : Array Name := #[`Acorn.Decisions, `AcornVerif.Decisions]

/-- The classes of one verdict-shaped definition, as the ownership audit reads them. -/
structure Classes where
  /-- A structure field or a function with a `Decidable` result. -/
  structural : Bool
  /-- The implementation of a contract of a decision registry. -/
  contract : Bool
  /-- Named by exactly one entry of `excluded`, which states the shape its type has and a
  reason that the computed facts support. -/
  listed : Bool
  deriving DecidableEq, Repr

/-- The decision of the inventory: the definition is in exactly one class. -/
def classified (classes : Classes) : Bool :=
  match classes.structural, classes.contract, classes.listed with
  | true, false, false | false, true, false | false, false, true => true
  | _, _, _ => false

/-- Exactly one of the three classes holds. -/
def ExactlyOne (classes : Classes) : Prop :=
  (classes.structural = true ∧ classes.contract = false ∧ classes.listed = false) ∨
    (classes.structural = false ∧ classes.contract = true ∧ classes.listed = false) ∨
    (classes.structural = false ∧ classes.contract = false ∧ classes.listed = true)

/-- The inventory decision accepts exactly a definition in exactly one class. The proof is by
cases over the eight values of the three classes. -/
theorem classified_iff (classes : Classes) : classified classes = true ↔ ExactlyOne classes := by
  rcases classes with ⟨_ | _, _ | _, _ | _⟩ <;> simp [classified, ExactlyOne]

/-- The inventory decision is sound and complete for "in exactly one class", with a
structural definition as the accepted input and a definition in no class as the refused one.
`AcornTools` is outside the Regula claim, so the Regula audit does not report this contract;
the ownership audit requires it by name. -/
theorem classified_decides :
    Regula.ExecutableContract classified (Regula.Decides (· = true) ExactlyOne) :=
  ⟨.of_iff classified_iff ⟨⟨true, false, false⟩, rfl⟩
    ⟨⟨false, false, false⟩, Bool.false_ne_true⟩⟩

/-- The compiled name of a private definition of a module. -/
def hidden (module user : Name) : Name := mkPrivateNameCore module user

/-- Every verdict-shaped definition of the claimed libraries that is neither structural nor
the implementation of a contract, with the shape of its type and its reason. -/
def excluded : Array (Name × Shape × Reason) := #[
  (`AcornVerif.CurrentOak.continuation, .dependent, .model),
  (`Acorn.Host.CertificateSearch.Findings.far._default, .dependent, .default),
  (`Acorn.Host.CertificateSearch.Findings.gold._default, .dependent, .default),
  (`Acorn.Host.CertificateSearch.Findings.near._default, .dependent, .default),
  (`Acorn.Host.CertificateSearch.Findings.stone._default, .dependent, .default),
  (`Acorn.Host.CertificateSearch.Findings.wood._default, .dependent, .default),
  (`Acorn.Host.Endurance.Reduction.first._default, .fixed, .default),
  (`Acorn.Host.Endurance.Reduction.last._default, .fixed, .default),
  (`Acorn.Host.RunnerResources.checkpointBytes._default, .fixed, .default),
  (`Acorn.Host.RunnerResources.checkpointWriteUs._default, .fixed, .default),
  (`Acorn.Host.StepResult.ate._default, .fixed, .default),
  (`Acorn.Host.StepResult.crafted._default, .fixed, .default),
  (`Acorn.Host.StepResult.done._default, .fixed, .default),
  (`Acorn.Host.StepResult.exhausted._default, .fixed, .default),
  (`Acorn.Host.StepResult.harvested._default, .fixed, .default),
  (`Acorn.Host.StepResult.moved._default, .fixed, .default),
  (`Acorn.Host.Viewer.Admission.newestTimestamp._default, .fixed, .default),
  (`Acorn.Host.Viewer.ControlDetail.abnormalExit._default, .fixed, .default),
  (`Acorn.Host.Viewer.ControlDetail.mapPartial._default, .fixed, .default),
  (`Acorn.Host.Viewer.LogStatus.checkpoint._default, .fixed, .default),
  (`Acorn.Host.Viewer.LogStatus.lastFailure._default, .fixed, .default),
  (`Acorn.Host.Viewer.OutputStatus.completion._default, .fixed, .default),
  (`NativeApp.OutcomeReport.saturated._default, .fixed, .default),
  (hidden `Acorn.Host.Viewer.Broadcast `Acorn.Host.Viewer.BroadcastState.adopted._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Broadcast `Acorn.Host.Viewer.BroadcastState.control._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Broadcast `Acorn.Host.Viewer.BroadcastState.waiting._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Broadcast `Acorn.Host.Viewer.BroadcastState.world._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Broadcast
      `Acorn.Host.Viewer.BroadcastState.worldPartial._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Broadcast `Acorn.Host.Viewer.IdentityWait.candidate._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Broadcast `Acorn.Host.Viewer.IdentityWait.refused._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Lifecycle
      `Acorn.Host.Viewer.Lifecycle.checkpointRefused._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Lifecycle `Acorn.Host.Viewer.Lifecycle.clearPending._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.LogPump `Acorn.Host.Viewer.LogState.accepting._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.ProcessOwner `Acorn.Host.Viewer.ProcessState.live._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Supervisor `Acorn.Host.Viewer.SupervisorState.failure._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Supervisor
      `Acorn.Host.Viewer.SupervisorState.mapWrittenRevision._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Supervisor
      `Acorn.Host.Viewer.SupervisorState.operatorStopped._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Supervisor
      `Acorn.Host.Viewer.SupervisorState.publicationReady._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.Supervisor
      `Acorn.Host.Viewer.SupervisorState.replacement._default, .fixed,
    .default),
  (hidden `Acorn.Host.Viewer.WorldMemory `Acorn.Host.Viewer.WorldMemory.incomplete._default, .fixed,
    .default),
  (`Acorn.AgentDriver.dispatch, .fixed, .unproved),
  (`Acorn.Checkpoint.temporaryPath, .fixed, .unproved),
  (`Acorn.Features.Assignment.retain, .dependent, .unproved),
  (`Acorn.Handcrafted.spatialPotential, .fixed, .unproved),
  (`Acorn.Host.AgentArguments.admit, .fixed, .unproved),
  (`Acorn.Host.AgentArguments.profile, .fixed, .unproved),
  (`Acorn.Host.AgentArguments.word, .fixed, .unproved),
  (`Acorn.Host.AnsiState.refresh, .dependent, .unproved),
  (`Acorn.Host.Attempt.prepare, .dependent, .unproved),
  (`Acorn.Host.BaselineAttempt.run, .dependent, .unproved),
  (`Acorn.Host.CertificateDriver.natural, .fixed, .unproved),
  (`Acorn.Host.CheckpointDriver.command, .fixed, .unproved),
  (`Acorn.Host.Cli.command, .fixed, .unproved),
  (`Acorn.Host.Cli.criterion, .fixed, .unproved),
  (`Acorn.Host.Cli.demo, .fixed, .unproved),
  (`Acorn.Host.Cli.dispatch, .fixed, .unproved),
  (`Acorn.Host.Cli.natural, .fixed, .unproved),
  (`Acorn.Host.Cli.profile, .fixed, .unproved),
  (`Acorn.Host.Cli.required, .fixed, .unproved),
  (`Acorn.Host.Cli.scan, .fixed, .unproved),
  (`Acorn.Host.Cli.side, .fixed, .unproved),
  (`Acorn.Host.Cli.unsigned, .fixed, .unproved),
  (`Acorn.Host.Endurance.energyQuantile, .fixed, .unproved),
  (`Acorn.Host.Endurance.mean, .fixed, .unproved),
  (`Acorn.Host.Viewer.BrowserColumn.view, .fixed, .unproved),
  (`Acorn.Host.Viewer.BrowserConversion.finite, .fixed, .unproved),
  (`Acorn.Host.Viewer.BrowserMath.Test.eval, .fixed, .unproved),
  (`Acorn.Host.Viewer.Buffer.pop, .dependent, .unproved),
  (`Acorn.Host.Viewer.Command.parse, .fixed, .unproved),
  (`Acorn.Host.Viewer.Envelope.parse, .fixed, .unproved),
  (`Acorn.Host.Viewer.HealthEnvelope.parse, .fixed, .unproved),
  (`Acorn.Host.Viewer.Identity.browserSafe, .fixed, .unproved),
  (`Acorn.Host.Viewer.Lifecycle.acceptsFailure, .fixed, .unproved),
  (`Acorn.Host.Viewer.Lifecycle.archiveIntent, .fixed, .unproved),
  (`Acorn.Host.Viewer.Lifecycle.archived, .fixed, .unproved),
  (`Acorn.Host.Viewer.Lifecycle.beginArchive, .fixed, .unproved),
  (`Acorn.Host.Viewer.Lifecycle.checkpointRefusedValue, .fixed, .unproved),
  (`Acorn.Host.Viewer.Lifecycle.reserve, .fixed, .unproved),
  (`Acorn.Host.Viewer.LineBytes.text, .fixed, .unproved),
  (`Acorn.Host.Viewer.LineDecoder.finish, .fixed, .unproved),
  (`Acorn.Host.Viewer.MapBytes.admit, .dependent, .unproved),
  (`Acorn.Host.Viewer.PersistedState.decode, .fixed, .unproved),
  (`Acorn.Host.Viewer.PersistedState.launch, .fixed, .unproved),
  (`Acorn.Host.Viewer.SensedEnvelope.parse, .fixed, .unproved),
  (`Acorn.Host.Viewer.ViewerOptions.decode, .fixed, .unproved),
  (`Acorn.Host.Viewer.WorldMemory.isIncomplete, .dependent, .unproved),
  (`Acorn.Host.Viewer.captureFromJson, .fixed, .unproved),
  (`Acorn.Host.Viewer.controlCommand, .fixed, .unproved),
  (`Acorn.Host.Viewer.coreIdentity, .fixed, .unproved),
  (`Acorn.Host.Viewer.coreIdentityFromJson, .fixed, .unproved),
  (`Acorn.Host.Viewer.decodeMap, .fixed, .unproved),
  (`Acorn.Host.Viewer.decodeMapRuns, .dependent, .unproved),
  (`Acorn.Host.Viewer.healthFromJson, .fixed, .unproved),
  (`Acorn.Host.Viewer.jsonBool, .fixed, .unproved),
  (`Acorn.Host.Viewer.jsonBrowserClock, .fixed, .unproved),
  (`Acorn.Host.Viewer.jsonField, .fixed, .unproved),
  (`Acorn.Host.Viewer.jsonWord, .fixed, .unproved),
  (`Acorn.Host.Viewer.mapRunsBase64, .fixed, .unproved),
  (`Acorn.Host.Viewer.residentBytes, .fixed, .unproved),
  (`Acorn.Host.Viewer.runWord, .fixed, .unproved),
  (`Acorn.Host.Viewer.sensedFromJson, .fixed, .unproved),
  (`Acorn.Host.Viewer.terrainFromJson, .fixed, .unproved),
  (`Acorn.Host.World.observeTile, .dependent, .unproved),
  (`Acorn.Host.controlWhitespace, .fixed, .unproved),
  (`Acorn.Host.fbm, .fixed, .unproved),
  (`Acorn.Host.foodDue, .fixed, .unproved),
  (`Acorn.Host.foodTrials, .dependent, .unproved),
  (`Acorn.Host.initializeDeer, .dependent, .unproved),
  (`Acorn.Host.octaveLoop, .fixed, .unproved),
  (`Acorn.Host.passiveChange, .dependent, .unproved),
  (`Acorn.Host.placeDeer, .dependent, .unproved),
  (`Acorn.Host.spawnFood, .dependent, .unproved),
  (`Acorn.Host.valueNoise, .fixed, .unproved),
  (`Acorn.Host.wanderDeer, .dependent, .unproved),
  (`Acorn.Host.wanderPopulation, .dependent, .unproved),
  (`Acorn.Json.Value.fields, .fixed, .unproved),
  (`Acorn.Json.Value.list, .fixed, .unproved),
  (`Acorn.Json.Value.natural, .fixed, .unproved),
  (`Acorn.Json.Value.optional, .fixed, .unproved),
  (`Acorn.Json.Value.text, .fixed, .unproved),
  (`Acorn.Json.decode, .dependent, .unproved),
  (`Acorn.Json.parse, .fixed, .unproved),
  (`Acorn.Json.take, .fixed, .unproved),
  (`Acorn.Json.text, .fixed, .unproved),
  (`Acorn.Json.texts, .fixed, .unproved),
  (`Acorn.Json.unicodeWhitespace, .fixed, .unproved),
  (`Acorn.Json.version, .fixed, .unproved),
  (`Acorn.Lifetime.DemonRecords.agreementRatio, .dependent, .composed),
  (`Acorn.WorldDriver.coordinate, .fixed, .unproved),
  (`Acorn.WorldDriver.dispatch, .fixed, .unproved),
  (`Acorn.WorldDriver.execute, .fixed, .unproved),
  (`Acorn.WorldDriver.executeTerrain, .fixed, .unproved),
  (`Acorn.WorldDriver.word, .fixed, .unproved),
  (`NativeApp.AuditArm.options, .fixed, .unproved),
  (`NativeApp.auditHex, .fixed, .unproved),
  (`NativeApp.auditOptions, .fixed, .unproved),
  (`NativeApp.buildIdentity, .fixed, .unproved),
  (`NativeApp.decodeBuildIdentity, .fixed, .unproved),
  (hidden `Acorn.Host.Viewer.Broadcast `Acorn.Host.Viewer.sameWorldRevision, .fixed, .unproved),
  (hidden `Acorn.Host.Viewer.FeatureTelemetry `Acorn.Host.Viewer.interestUnit, .dependent,
    .unproved),
  (hidden `Acorn.Host.Viewer.HttpServer `Acorn.Host.Viewer.singleHeader, .fixed, .unproved),
  (hidden `Acorn.Host.Viewer.MapCodec `Acorn.Host.Viewer.decodeHeader, .fixed, .unproved),
  (hidden `Acorn.Host.Viewer.MapCodec `Acorn.Host.Viewer.decodeRuns, .dependent, .unproved),
  (hidden `Acorn.Host.Viewer.ProcessOwner `Acorn.Host.Viewer.CommandInput.wasRequested, .fixed,
    .unproved),
  (hidden `Acorn.Host.Viewer.Supervisor `Acorn.Host.Viewer.terminationFailed, .fixed, .unproved),
  (hidden `Acorn.Host.Viewer.WorldMemory `Acorn.Host.Viewer.admitMapPrefix, .dependent, .unproved),
  (hidden `Acorn.Json `Acorn.Json.digits, .fixed, .unproved),
  (hidden `Acorn.Json `Acorn.Json.elements, .fixed, .unproved),
  (hidden `Acorn.Json `Acorn.Json.fields, .fixed, .unproved),
  (hidden `Acorn.Json `Acorn.Json.number, .fixed, .unproved),
  (hidden `Acorn.Json `Acorn.Json.quad, .fixed, .unproved),
  (hidden `Acorn.Json `Acorn.Json.require, .fixed, .unproved),
  (hidden `Acorn.Json `Acorn.Json.stringBody, .fixed, .unproved),
  (hidden `Acorn.Json `Acorn.Json.stringValue, .fixed, .unproved),
  (hidden `Acorn.Json `Acorn.Json.unicode, .fixed, .unproved),
  (hidden `Acorn.Json `Acorn.Json.value, .fixed, .unproved),
  (hidden `NativeApp.Build `NativeApp.hex, .dependent, .unproved),
  (`Acorn.Host.CertificateDriver.execute, .fixed, .composed),
  (`Acorn.Host.Viewer.WorldMemory.frame, .dependent, .composed),
  (`Acorn.Host.Viewer.authorizeCommand, .dependent, .composed),
  (`Acorn.Host.Viewer.controlTelemetryLine, .fixed, .composed),
  (`Acorn.Host.Viewer.coreTelemetryLine, .dependent, .composed),
  (`Acorn.Lifetime.SumCount.admit, .dependent, .composed),
  (`Acorn.LogStepSize.admit, .dependent, .composed),
  (`Acorn.Prediction.admit, .dependent, .composed),
  (`Acorn.Host.CertificateSearch.Findings.complete, .dependent, .proposal),
  (`Acorn.Host.CertificateSearch.arrivalDirection, .fixed, .proposal),
  (`Acorn.Host.CertificateSearch.behind, .dependent, .proposal),
  (`Acorn.Host.CertificateSearch.inGoalBox, .dependent, .proposal),
  (`Acorn.Host.CertificateSearch.neighbor, .dependent, .proposal),
  (`Acorn.Host.CertificateSearch.region, .fixed, .proposal),
  (`Acorn.Host.Viewer.instBEqCapture.beq, .fixed, .derived),
  (`Acorn.Host.Viewer.instBEqCommand.beq, .fixed, .derived),
  (`Acorn.Host.Viewer.instBEqCoreIdentity.beq, .fixed, .derived),
  (`Acorn.Host.Viewer.instBEqDesired.beq, .fixed, .derived),
  (`Acorn.Host.Viewer.instBEqIdentity.beq, .fixed, .derived),
  (`Acorn.Host.Viewer.instBEqIntake.beq, .fixed, .derived),
  (`Acorn.Host.Viewer.instBEqNewAgentOrigin.beq, .fixed, .derived),
  (`Acorn.Host.Viewer.instBEqPersistedState.beq, .fixed, .derived),
  (`Acorn.Host.Viewer.instBEqPhase.beq, .fixed, .derived),
  (`Acorn.Host.Viewer.instBEqRunFile.beq, .fixed, .derived),
  (`Acorn.Host.instBEqAction.beq, .fixed, .derived),
  (`Acorn.Host.instBEqBoxPosition.beq, .dependent, .derived),
  (`Acorn.Host.instBEqCheckpointStatus.beq, .fixed, .derived),
  (`Acorn.Host.instBEqDirection.beq, .fixed, .derived),
  (`Acorn.Host.instBEqPosition.beq, .fixed, .derived),
  (`Acorn.Host.instBEqResearchProfile.beq, .fixed, .derived),
  (`Acorn.Host.instBEqStopState.beq, .fixed, .derived),
  (`Acorn.Host.instBEqTileKind.beq, .fixed, .derived),
  (`NativeApp.instBEqAuditReceipt.beq, .fixed, .derived),
  (`AcornVerif.Checkpoint.authorize, .dependent, .model),
  (`AcornVerif.CurrentGridWorld.advance, .dependent, .model),
  (`AcornVerif.CurrentGridWorld.physicalPath, .dependent, .model),
  (`AcornVerif.CurrentGridWorld.physicalStep, .dependent, .model),
  (`AcornVerif.CurrentLearner.finalPhase, .dependent, .model),
  (`AcornVerif.CurrentLearner.nextReady, .dependent, .model),
  (`AcornVerif.CurrentSpawn.reads, .dependent, .model),
  (`AcornVerif.CurrentStep.passable, .fixed, .model),
  (`AcornVerif.CurrentTemporal.committedRun, .dependent, .model),
  (`AcornVerif.CurrentTemporal.leftToServe, .dependent, .model),
  (`AcornVerif.CurrentTemporal.runPrefix, .dependent, .model),
  (`AcornVerif.CurrentTemporal.serveSteps, .dependent, .model),
  (`AcornVerif.GridCorrespondence.Direct.restore, .dependent, .model),
  (`AcornVerif.GridCorrespondence.Direct.step, .dependent, .model),
  (`AcornVerif.Resource.WordTree.admit, .dependent, .model),
  (`AcornVerif.TemporalSupport.outcomes, .dependent, .model),
  (`Acorn.Features.ExploratoryRun.serve, .dependent,
    .named `Acorn.Features.ExploratoryRun.serve_exact),
  (`Acorn.Handcrafted.Agent.input, .dependent, .named `AcornVerif.CurrentAgent.edge_contract),
  (`Acorn.Handcrafted.Agent.runPrefix, .dependent,
    .named `Acorn.Handcrafted.Agent.clear_suffix),
  (`Acorn.Handcrafted.AgentConstruction.execute, .dependent,
    .named `AcornVerif.CurrentAgent.native_prefix),
  (`Acorn.Handcrafted.TemporalControl.atBoundary, .dependent,
    .named `Acorn.Handcrafted.TemporalControl.atBoundary_assigns),
  (`Acorn.Handcrafted.TemporalControl.dispatchMeta, .dependent,
    .named `Acorn.Handcrafted.TemporalControl.dispatchMeta_eq),
  (`Acorn.Handcrafted.TemporalControl.select, .dependent,
    .named `AcornVerif.CurrentTemporal.step_executing),
  (`Acorn.Handcrafted.TemporalControl.selectWithOperations, .dependent,
    .named `Acorn.Handcrafted.TemporalControl.primitive_undrawn),
  (`Acorn.Handcrafted.TemporalControl.serve, .dependent,
    .named `Acorn.Handcrafted.TemporalControl.select_drawn),
  (`Acorn.Handcrafted.TemporalControl.step, .dependent,
    .named `Acorn.Handcrafted.TemporalControl.step_episodes),
  (`Acorn.Host.AnsiState.tick, .dependent, .named `Acorn.Host.AnsiState.tick_observation),
  (`Acorn.Host.Attempt.finish, .dependent, .named `Acorn.Host.Attempt.finish_position),
  (`Acorn.Host.Attempt.sense, .dependent, .named `AcornVerif.CurrentRunner.sense_none),
  (`Acorn.Host.Attempt.tick, .dependent, .named `Acorn.Host.Attempt.tick_finished),
  (`Acorn.Host.BaselineAttempt.tick, .dependent,
    .named `AcornVerif.CurrentRunner.idle_corresponds),
  (`Acorn.Host.OwnedStep.environment, .dependent,
    .named `Acorn.Host.SelectedStep.owned_commit),
  (`Acorn.Host.PreparedStep.commit, .dependent, .named `AcornVerif.CurrentRunner.commit_clock),
  (`Acorn.Host.PreparedStep.environment, .dependent,
    .named `Acorn.Host.SelectedStep.owned_commit),
  (`Acorn.Host.World.initial, .dependent, .named `Acorn.Host.World.initial_fields),
  (`Acorn.Host.World.observe, .dependent, .named `Acorn.Host.World.observe_task),
  (`Acorn.Host.considerSpawn, .dependent,
    .named `AcornVerif.CurrentSpawn.considerSpawn_contract),
  (`Acorn.Host.countKindNear, .dependent, .named `AcornVerif.CurrentSpawn.countKindNear_eq),
  (`Acorn.Host.runBaselineCampaign, .dependent,
    .named `AcornVerif.CurrentRunner.baseline_campaign_finishes),
  (`Acorn.Host.runRandomBaseline, .fixed, .named `AcornVerif.CurrentRunner.baseline_finishes),
  (`Acorn.Host.selectSpawn, .dependent, .named `AcornVerif.CurrentSpawn.initial_spawn),
  (`Acorn.Features.Occupancy.executing, .dependent,
    .named `Acorn.Features.Occupancy.afterOption_executing),
  (`Acorn.Features.RankedFeatures.position, .dependent,
    .named `Acorn.Features.RankedFeatures.position_complete),
  (`Acorn.Features.best, .dependent, .named `Acorn.Features.best_spec),
  (`Acorn.Features.kept, .dependent, .named `Acorn.Features.entrants_le_open),
  (`Acorn.Handcrafted.TemporalControl.activeSlot, .dependent,
    .named `Acorn.Handcrafted.TemporalControl.boundary_episodes),
  (`Acorn.Handcrafted.TemporalControl.takeoverValue, .dependent,
    .named `AcornVerif.CurrentTemporal.takeover_none),
  (`Acorn.Handcrafted.skillOfMeta, .fixed,
    .named `Acorn.Handcrafted.TemporalControl.dispatchMeta_eq),
  (`Acorn.Features.Interface.reserved, .fixed,
    .named `Acorn.Handcrafted.Grid.sensorWords_clear),
  (`Acorn.Features.Occupancy.free, .dependent,
    .named `Acorn.Features.FeatureRuntime.retire_occupied),
  (`Acorn.Features.OptionActivation.learning, .dependent,
    .named `Acorn.Features.Skill.stepTemporal_eq),
  (`Acorn.Features.TemporalDecision.own, .dependent,
    .named `Acorn.Handcrafted.TemporalControl.finish_credit),
  (`Acorn.Handcrafted.FeatureProfile.ranksSubtasks, .fixed,
    .named `Acorn.Handcrafted.TemporalControl.atBoundary_assigns),
  (`Acorn.Handcrafted.FeatureProfile.usesHierarchy, .fixed,
    .named `Acorn.Handcrafted.TemporalControl.finish_eq),
  (`Acorn.Handcrafted.askedBy, .dependent,
    .named `Acorn.Handcrafted.TemporalControl.finish_skill)
]

/-- The excluded definitions that the implementation of a registered decision reaches and that
no written theorem names. None has a contract: the contract of the registered decision that
reaches it is the evidence. The audit computes the reach of every excluded definition and
requires it to agree with this list. -/
def relied : Array Name := #[
  `Acorn.Host.fbm, `Acorn.Host.octaveLoop, `Acorn.Host.valueNoise, `Acorn.Host.foodDue,
  `Acorn.Host.foodTrials, `Acorn.Host.passiveChange, `Acorn.Host.spawnFood,
  `Acorn.Host.wanderDeer, `Acorn.Host.wanderPopulation,
  `Acorn.Lifetime.DemonRecords.agreementRatio, `Acorn.Lifetime.SumCount.admit,
  `Acorn.Prediction.admit,
  `Acorn.Host.Viewer.instBEqPhase.beq, `Acorn.Host.instBEqAction.beq,
  `Acorn.Host.instBEqBoxPosition.beq, `Acorn.Host.instBEqCheckpointStatus.beq,
  `Acorn.Host.instBEqTileKind.beq
]

/-- The size of `relied`. A new member changes this number, which is reviewed. -/
theorem relied_count : relied.size = 17 := by decide

/-- The entries that a theorem names. A new entry changes this number, which is reviewed. -/
theorem named_count : (excluded.filter fun entry => entry.2.2.standing?.isSome).size = 39 := by
  decide +kernel

/-- The entries with a reason that has no standing theorem. -/
theorem plain_count : (excluded.filter fun entry => entry.2.2.standing?.isNone).size = 206 := by
  decide +kernel

/-- The result heads that make a definition verdict-shaped. -/
def verdictHead (name : Name) : Bool :=
  name == ``Bool || name == ``Option || name == ``Except || name == ``Decidable

/-- The certificate search module, whose functions propose certificates. -/
def searchModule : Name := `Acorn.Host.CertificateSearch

/-- What the walk of the compiled environment reads about one verdict-shaped definition. -/
structure Candidate where
  /-- The definition, by its compiled name. -/
  name : Name
  /-- The module that owns it. -/
  owner : Name
  /-- The shape of its type. -/
  shape : Shape
  /-- A structure field or a function with a `Decidable` result. -/
  structural : Bool
  /-- A function with a `Decidable` result. -/
  decidable : Bool
  /-- The comparison of a derived instance. -/
  generated : Bool
  /-- The default of a structure field that is not a function. -/
  fieldDefault : Bool
  /-- The constants its body names. -/
  uses : Array Name

/-- The form of one part of a statement with no kind. A strong form is given only to an exact
shape that `leafForm` reads completely. Every other part that names the function outside a
marker is `unclassified`, which says nothing about the strength of the part. -/
inductive Form where
  /-- The part quantifies over exactly the inputs of the function, and its body is an
  equivalence between an equation about the result at those inputs and a proposition that
  does not name the function. It fixes, at every input, whether that equation holds. -/
  | verdict
  /-- The part quantifies over exactly the inputs of the function, and its body is an equation
  between the result at those inputs, or its presence, and a term that does not name the
  function. It fixes the result, or its presence, at every input. -/
  | result
  /-- Any other part that names the function outside a marker. -/
  | unclassified
  deriving DecidableEq, Repr

/-- The name of a form in the output of the audit. -/
def Form.label : Form → String
  | .verdict => "exact verdict" | .result => "exact result" | .unclassified => "not classified"

/-- One marked witness: the contract, the decision function, the side, and the constants of
this repository that its input names. The audit counts it only when no input depends on the
decision function. -/
structure Witness where
  /-- The contract that states the witness. -/
  contract : Name
  /-- The decision function. -/
  implementation : Name
  /-- Whether the witness is an accepted input. A refused input otherwise. -/
  accepted : Bool
  /-- The constants of this repository that the arguments of the function name. -/
  inputs : Array Name

/-- What the contracts of the registries state about one decision function. -/
structure Registered where
  /-- One of its contracts is a decision kind. -/
  kind : Bool := false
  /-- One of its contracts is a two-way kind, or carries a marked accepted input that the
  audit examined. -/
  accepted : Bool := false
  /-- One of its contracts is a two-way kind, or carries a marked refused input that the
  audit examined. -/
  refused : Bool := false
  /-- One of its contracts proves that every input is refused, so no accepted input exists. -/
  neverAccepted : Bool := false
  /-- One of its contracts proves that every input is accepted, so no refused input exists. -/
  neverRefused : Bool := false

/-- One statement with no kind: its contract, its decision function and the form of each of
its parts that names the function outside a marker. -/
structure Statement where
  /-- The contract. -/
  contract : Name
  /-- The decision function. -/
  implementation : Name
  /-- The forms of the parts, in the order of the statement. None for a statement that holds
  markers only. -/
  forms : Array Form

/-- What the walk has read so far. -/
structure Observed where
  /-- Verdict-shaped definitions of the surveyed modules. -/
  candidates : Array Candidate := #[]
  /-- The decision functions that the registries state a contract about. -/
  contracts : NameMap Registered := {}
  /-- Constants that the statement of a written theorem outside the registries names. -/
  mentioned : NameSet := {}
  /-- Excluded definitions whose standing theorem was read and names them. -/
  standing : NameSet := {}
  /-- Verdict-shaped constants that left the domain, by the name of their relationship. -/
  certified : Std.HashMap String Nat := {}
  /-- Definitions outside the search module that name one of its constants, with the
  constants their bodies name. -/
  searchers : Array (Name × Array Name) := #[]
  /-- The constants that the body of each definition of the surveyed modules names. -/
  bodies : NameMap (Array Name) := {}
  /-- The statements with no kind. -/
  statements : Array Statement := #[]
  /-- The marked witnesses of the statements with no kind. -/
  witnesses : Array Witness := #[]

/-- Join what two contracts state about one function. -/
def Registered.add (left right : Registered) : Registered :=
  ⟨left.kind || right.kind, left.accepted || right.accepted, left.refused || right.refused,
    left.neverAccepted || right.neverAccepted, left.neverRefused || right.neverRefused⟩

/-- Join the observations of two environments. -/
def Observed.add (left right : Observed) : Observed :=
  { candidates := left.candidates ++ right.candidates
    contracts := right.contracts.foldl (fun all name stated =>
      all.insert name (((all.find? name).getD {}).add stated)) left.contracts
    mentioned := right.mentioned.foldl (fun all name => all.insert name) left.mentioned
    standing := right.standing.foldl (fun all name => all.insert name) left.standing
    certified := right.certified.fold (fun all label count =>
      all.insert label (all.getD label 0 + count)) left.certified
    searchers := left.searchers ++ right.searchers
    bodies := right.bodies.foldl (fun all name uses => all.insert name uses) left.bodies
    statements := left.statements ++ right.statements
    witnesses := left.witnesses ++ right.witnesses }

/-- What the one telescope of the inventory reads from a type. Every count of arguments in
this module comes from here. -/
structure Signature where
  /-- The head constant of the result, with reducible definitions unfolded. -/
  head : Name
  /-- The head constant of the first argument of the result: the type that a class instance
  is about. -/
  about : Option Name
  /-- The number of arguments, with reducible definitions unfolded. -/
  arguments : Nat
  /-- Whether a binder type or the result names one of the arguments. -/
  shape : Shape

/-- The signature of a type: its arguments and its result after reducible definitions are
unfolded. A type whose result has no head constant has none. -/
def signatureOf (type : Expr) : MetaM (Option Signature) :=
  forallTelescopeReducing type fun arguments body => do
    let body ← whnfR body
    let some head := body.getAppFn.constName? | return none
    let mut dependent := false
    for argument in arguments do
      if body.containsFVar argument.fvarId! then dependent := true
      let declared ← argument.fvarId!.getDecl
      for other in arguments do
        if declared.type.containsFVar other.fvarId! then dependent := true
    return some
      { head, about := (body.getAppArgs[0]?).bind (·.getAppFn.constName?)
        arguments := arguments.size, shape := if dependent then .dependent else .fixed }

/-- The source range that Lean recorded for a declaration made by a declaration command. -/
def sourceRange (env : Environment) (name : Name) : Option DeclarationRange :=
  (declRangeExt.find? (level := .server) env name).map (·.range)

/-- Whether one recorded range lies inside another. -/
def within (inner outer : DeclarationRange) : Bool :=
  (outer.pos.line < inner.pos.line ||
      (outer.pos.line == inner.pos.line && outer.pos.column ≤ inner.pos.column)) &&
    (inner.endPos.line < outer.endPos.line ||
      (inner.endPos.line == outer.endPos.line && inner.endPos.column ≤ outer.endPos.column))

/-- Whether Lean generated a theorem, by a relationship that the environment records: a proof
field of a structure, an equation or unfolding theorem under a reserved name, or the
injectivity or size theorem that Lean names for a recorded constructor. Every other theorem
counts as written. A proof that the elaborator abstracted from a declaration counts as
written too, so a definition that only such a proof names cannot be `unproved`; that errs
toward a contract. -/
def generatedTheorem (env : Environment) (name : Name) : Bool :=
  (env.getProjectionFnInfo? name).isSome || isReservedName env name ||
    (match env.find? name.getPrefix with
      | some (.ctorInfo _) =>
        name == Lean.Meta.mkInjectiveTheoremNameFor name.getPrefix ||
          name == Lean.Meta.mkInjectiveEqTheoremNameFor name.getPrefix ||
          name == Lean.Meta.mkSizeOfSpecLemmaName name.getPrefix
      | _ => false)

/-- Whether a theorem is written in the source. -/
def written (env : Environment) (name : Name) : Bool := !generatedTheorem env name

/-- The relationship by which a verdict-shaped constant leaves the domain: it is a companion
that a recursion compiler made for a parent declaration. The parent has equation data of
that compiler in the environment, the name is the one the compiler derives from the parent,
and the content agrees: a companion that is another body of the parent has the parent's
signature, and a companion that is one step of the recursion is applied by the parent's
body. A flag, a name or a position alone gives no relationship. -/
def companion? (env : Environment) (name : Name) (info : ConstantInfo) : Option String :=
  let parent := name.getPrefix
  match env.find? parent with
  | none => none
  | some parentInfo =>
    let structural := (Lean.Elab.Structural.eqnInfoExt.find? env parent).isSome
    let wellFounded := Lean.Elab.WF.eqnInfoExt.find? env parent
    let signature := info.type == parentInfo.type && info.levelParams == parentInfo.levelParams
    let applied := (parentInfo.value?.map (·.getUsedConstants.contains name)).getD false
    if structural && signature && name == Lean.Meta.mkSmartUnfoldingNameFor parent then
      some "unfolding body of a structural recursion"
    else if (structural || wellFounded.isSome) && signature && info.isPartial &&
        name == Lean.Compiler.mkUnsafeRecName parent then
      some "compiled body of a recursion"
    else if structural && applied && name == .str parent "_f" then
      some "step of a structural recursion"
    else if applied && wellFounded.any (·.declNameNonRec == name) then
      some "step of a well-founded recursion"
    else none

/-- Whether a definition is the default value of a structure field that is not a function:
the field is a recorded projection, the name is the one Lean derives for its default, and
the projection takes the parameters of the structure and the structure, and nothing more.
The count is the count of `signatureOf`, so a function type behind a reducible definition
is a function type. -/
def storedDefault (env : Environment) (name : Name) : MetaM Bool := do
  let field := name.getPrefix
  let some projection := env.getProjectionFnInfo? field | return false
  unless name == Lean.mkDefaultFnOfProjFn field do return false
  let some fieldInfo := env.find? field | return false
  let some signature ← signatureOf fieldInfo.type | return false
  return signature.arguments == projection.numParams + 1

/-- Whether a definition is the comparison that a `deriving` clause generated: it is the
`beq` of a registered instance of `BEq` for a type of the same module, and the definition
and the instance both lie inside the declaration of that type. The relationship to the
instance and to the type is validated. That the comparison is generated is inferred from the
recorded ranges, because Lean records no relation between a `deriving` clause and what it
generates. -/
def derivedComparison (env : Environment) (name : Name) : MetaM Bool := do
  let .str parent "beq" := name | return false
  let some instanceInfo := env.find? parent | return false
  let some own := sourceRange env name | return false
  let some instanceRange := sourceRange env parent | return false
  let some signature ← signatureOf instanceInfo.type | return false
  let some compared := signature.about | return false
  unless signature.head == ``BEq && Lean.Meta.isInstanceCore env parent do return false
  unless env.getModuleIdxFor? compared == env.getModuleIdxFor? name do return false
  let some outer := sourceRange env compared | return false
  return within own outer && within instanceRange outer

/-- The decision kinds of Regula. Its audit checks a witness of each kind and the independence
of its specification from the implementation. -/
def kinds : Array Name :=
  #[``Regula.Decides, ``Regula.DecidesSoundly, ``Regula.DecidesCompletely]

/-- The body of a contract condition, below its binders. -/
def conditionBody : Expr → Expr
  | .lam _ _ body _ => conditionBody body
  | condition => condition

/-- A contract condition that is a decision kind: after its binders, its head is one of the
kinds. A statement of any other form is a requirement that the Regula audit does not check
for witnesses or independence. -/
def isKind (condition : Expr) : Bool :=
  ((conditionBody condition).getAppFn.constName?).any kinds.contains

/-- The marker propositions of the registries for an accepted and for a refused input. Each
registry declares its own pair, because no module imports a registry. -/
def acceptanceMarkers : Array Name := #[`Acorn.Decisions.Accepts, `AcornVerif.Decisions.Accepts]

@[inherit_doc acceptanceMarkers]
def refusalMarkers : Array Name := #[`Acorn.Decisions.Refuses, `AcornVerif.Decisions.Refuses]

/-- The acceptance predicates that a witness can use: the result is `true`, is present, or
is not an error. -/
def standardAccepts : Expr → Bool
  | .lam _ _ body _ =>
    match body.eq? with
    | some (type, result, expected) =>
      type.isConstOf ``Bool && expected.isConstOf ``Bool.true &&
        (result == .bvar 0 ||
          ((result.isAppOf ``Option.isSome || result.isAppOf ``Except.isOk) &&
            result.appArg! == .bvar 0))
    | none => false
  | _ => false

/-- The conjuncts of a proposition at its top level. -/
def conjuncts : Expr → Array Expr
  | .app (.app (.const ``And _) left) right => conjuncts left ++ conjuncts right
  | proposition => #[proposition]

/-- The constants that an expression names: its constants and the structures of its
projections. -/
def namesOf (expression : Expr) : Array Name :=
  let found : NameSet := runST fun σ => do
    let visit : StateT NameSet (ST σ) Unit := expression.forEach' fun part => do
      match part with
      | .const name _ => modify (·.insert name)
      | .proj name _ _ => modify (·.insert name)
      | _ => pure ()
      return true
    return (← visit.run {}).2
  found.foldl (fun all name => all.push name) #[]

/-- The constants that a constant depends on, as the kernel reads it: those of its type,
those of its value when it has one, and the parts of its inductive declaration. The match is
over every constructor of `ConstantInfo`, so no kind of constant is left unread. The value of
an opaque constant and the value of a theorem are read. -/
def dependencies (info : ConstantInfo) : Array Name :=
  let type := namesOf info.type
  match info with
  | .axiomInfo _ | .quotInfo _ => type
  | .defnInfo value => type ++ namesOf value.value ++ value.all.toArray
  | .thmInfo value => type ++ namesOf value.value ++ value.all.toArray
  | .opaqueInfo value => type ++ namesOf value.value ++ value.all.toArray
  | .inductInfo value =>
    type ++ value.ctors.toArray ++ value.all.toArray ++ #[mkRecName value.name]
  | .ctorInfo value => type.push value.induct
  | .recInfo value =>
    value.rules.foldl (fun all rule => all ++ namesOf rule.rhs) (type ++ value.all.toArray)

/-- The roots of the module names of the libraries of this repository. No other library
imports one of them, so a constant of another library depends on no constant of these. -/
def ownRoots : Array Name := #[`Acorn, `AcornVerif, `NativeApp, `Bootstrap, `AcornTools]

/-- Whether a constant belongs to a library of this repository. A constant with no recorded
module counts as one. -/
def own (env : Environment) (name : Name) : Bool :=
  match (env.getModuleIdxFor? name).bind fun index => env.header.moduleNames[index.toNat]? with
  | some module => ownRoots.contains module.getRoot
  | none => true

/-- The inputs of the marked witnesses of a condition, for one of the two marker sets: for
each conjunct at the top level of the condition whose head is a marker, whose predicate is a
standard one and whose result is an application of the bound implementation to arguments that
do not name the bound variable, the constants that those arguments name. Such a conjunct is
below no quantifier and no hypothesis. Whether an input depends on the decision function is
decided later, from the dependencies of all constants (`reaches`). -/
def witnessInputs (markers : Array Name) : Expr → Array (Array Name)
  | .lam _ _ body _ =>
    (conjuncts body).filterMap fun fact =>
      if (fact.getAppFn.constName?).any markers.contains then
        match fact.getAppArgs with
        | #[_, predicate, result] =>
          if standardAccepts predicate && result.getAppFn == .bvar 0 &&
              result.getAppArgs.all fun argument => !argument.hasLooseBVar 0 then
            some (result.getAppArgs.foldl (fun all argument => all ++ namesOf argument) #[])
          else none
        | _ => none
      else none
  | _ => #[]

/-- The dependencies of every constant of this repository that one of the start constants
reaches, read from an environment that holds them. A constant that the environment does not
hold gets no entry, so `reaches` refuses an input that reaches it. Each constant is entered at
most once, so the walk ends within the number of constants of the environment. -/
def closure (env : Environment) (start : Array Name) : NameMap (Array Name) := Id.run do
  let mut table : NameMap (Array Name) := {}
  let mut seen : NameSet := {}
  let mut pending := start
  for _ in [0:env.constants.fold (fun count _ _ => count + 1) 1] do
    let mut next : Array Name := #[]
    for name in pending do
      if seen.contains name then continue
      seen := seen.insert name
      let some info := env.find? name | continue
      let used := (dependencies info).filter (own env)
      table := table.insert name used
      for other in used do
        unless seen.contains other do next := next.push other
    if next.isEmpty then break
    pending := next
  return table

/-- Whether one of the start constants depends on the target: it is the target, or one of
its dependencies depends on the target. `uses` gives the dependencies of a constant of this
repository, and none for a constant that the audit did not read. The answer for such a
constant is that the target is reached, which refuses the input. The walk enters each
constant once; when the fuel ends before the walk does, the answer is also that the target is
reached. -/
def reaches (uses : Name → Option (Array Name)) (target : Name) (start : Array Name)
    (fuel : Nat) : Bool := Id.run do
  let mut seen : NameSet := {}
  let mut pending := start
  for _ in [0:fuel] do
    let mut next : Array Name := #[]
    for name in pending do
      if name == target then return true
      if seen.contains name then continue
      seen := seen.insert name
      let some used := uses name | return true
      for other in used do
        unless seen.contains other do next := next.push other
    if next.isEmpty then return false
    pending := next
  return true

/-- The markers of a proved obstruction: no accepted input exists, or no refused input exists.
Each takes the proposition that proves it. -/
def noAcceptedMarkers : Array Name :=
  #[`Acorn.Decisions.NoAccepted, `AcornVerif.Decisions.NoAccepted]

@[inherit_doc noAcceptedMarkers]
def noRefusedMarkers : Array Name :=
  #[`Acorn.Decisions.NoRefused, `AcornVerif.Decisions.NoRefused]

/-- The body of a proposition below its quantifiers, with their number. -/
def quantified : Nat → Expr → Nat × Expr
  | count, .forallE _ _ body _ => quantified (count + 1) body
  | count, body => (count, body)

/-- Whether a term is the function applied to exactly the quantified variables, each once
and in order. The function is the loose variable `count`, below `count` quantifiers. A
hypothesis would be one more quantifier that is not an argument, so no quantifier is a
hypothesis, and each domain is the type of an argument of the function. -/
def atInputs (count : Nat) (term : Expr) : Bool :=
  count != 0 && term.getAppFn == .bvar count &&
    term.getAppArgs == (Array.range count).reverse.map Expr.bvar

/-- Whether a proposition states a marked fact for every input of the bound function: a
telescope of quantifiers whose body applies one of the markers, with a standard predicate, to
the function at exactly the quantified variables, each once and in order. A hypothesis would
be one more quantifier that is not an argument, so no hypothesis restricts the inputs. -/
def everyInput (markers : Array Name) (claim : Expr) : Bool :=
  let (count, body) := quantified 0 claim
  (body.getAppFn.constName?).any markers.contains &&
    (match body.getAppArgs with
      | #[_, predicate, result] => standardAccepts predicate && atInputs count result
      | _ => false)

/-- Whether a requirement with no kind carries a proved obstruction with one of the given
markers: a conjunct at the top level of the condition that applies the marker to a
proposition which states, for every input, a fact with one of the fact markers. -/
def proved (markers facts : Array Name) : Expr → Bool
  | .lam _ _ body _ =>
    (conjuncts body).any fun fact =>
      (fact.getAppFn.constName?).any markers.contains &&
        (match fact.getAppArgs with
          | #[claim] => everyInput facts claim
          | _ => false)
  | _ => false

/-- The function that a kind is stated about, below its `Function.uncurry` wrappers. -/
def decided : Expr → Expr
  | .app (.app (.app (.app (.app (.const ``Function.uncurry _) _) _) _) function) pair =>
    .app (decided function) pair
  | .app (.app (.app (.app (.const ``Function.uncurry _) _) _) _) function => decided function
  | function => function

/-- Whether a condition is a kind about the implementation that it binds: a condition that is
not a function is a kind applied to its acceptance predicate and specification, which the
contract applies to the implementation; a condition that binds the implementation states the
kind about that bound variable itself, below `Function.uncurry` and nothing more. A kind about
another function, or about a definition that calls the implementation, is not a kind of this
implementation. -/
def kindAbout (condition : Expr) : Option Name :=
  match condition with
  | .lam _ _ body _ =>
    match body.getAppFn.constName?, body.getAppArgs.back? with
    | some kind, some function =>
      if kinds.contains kind && decided function == .bvar 0 then some kind else none
    | _, _ => none
  | applied =>
    match applied.getAppFn.constName? with
    | some kind => if kinds.contains kind then some kind else none
    | none => none

/-- What one contract condition states, apart from its marked witnesses, whose inputs are
examined later. A two-way kind fixes the verdict at every input (`Regula.Decides.iff`) and
states that both outcomes occur, so it counts for both sides. A one-way kind fixes one
direction only, and the input of its witness is inside a proof, so it counts for no side: the
function gets its two witnesses from marked facts. -/
def registered (condition : Expr) : Registered :=
  match kindAbout condition with
  | some ``Regula.Decides => { kind := true, accepted := true, refused := true }
  | some ``Regula.DecidesSoundly | some ``Regula.DecidesCompletely => { kind := true }
  | _ =>
    { neverAccepted := proved noAcceptedMarkers refusalMarkers condition
      neverRefused := proved noRefusedMarkers acceptanceMarkers condition }

/-- Every marker of a registry: a conjunct with one of these heads is a witness or an
obstruction and not a part of the statement. -/
def markers : Array Name :=
  acceptanceMarkers ++ refusalMarkers ++ noAcceptedMarkers ++ noRefusedMarkers

/-- An equation between the result of the function at exactly the quantified inputs, or
`Option.isSome` or `Except.isOk` of that result, and a term that does not name the function. -/
def equationAtInputs (count : Nat) (proposition : Expr) : Bool :=
  let result (side : Expr) : Bool :=
    atInputs count
      (if side.isAppOfArity ``Option.isSome 2 || side.isAppOfArity ``Except.isOk 3 then
        side.appArg! else side)
  match proposition.eq? with
  | some (_, left, right) =>
    (result left && !right.hasLooseBVar count) || (result right && !left.hasLooseBVar count)
  | none => false

/-- The form of a leaf that names the function, below `count` quantifiers. The two strong
forms are the two exact shapes; nothing else has a strong form. -/
def leafForm (count : Nat) (leaf : Expr) : Form :=
  match leaf.iff? with
  | some (left, right) =>
    if (equationAtInputs count left && !right.hasLooseBVar count) ||
        (equationAtInputs count right && !left.hasLooseBVar count) then .verdict
    else .unclassified
  | none => if equationAtInputs count leaf then .result else .unclassified

/-- The forms of the leaves of a proposition that name the function, which is the loose
variable `count`. The walk reads a quantifier and a conjunction and nothing more. A quantifier
distributes over a conjunction, so each leaf is a statement below the quantifiers above it,
and `leafForm` requires that those quantifiers are exactly the inputs of the function. A
quantifier whose domain names the function is a hypothesis about the function: the
proposition is then one part that is not classified. A leaf that does not name the function
makes no claim about it. A marker has no special reading here, so a marker below a quantifier
is a part that is not classified. -/
def formsOf (count : Nat) : Expr → Array Form
  | .forallE _ domain body _ =>
    if domain.hasLooseBVar count then #[.unclassified] else formsOf (count + 1) body
  | .app (.app (.const ``And _) left) right => formsOf count left ++ formsOf count right
  | leaf => if leaf.hasLooseBVar count then #[leafForm count leaf] else #[]

/-- The forms of the parts of a contract condition with no kind. A conjunct at the top level
whose head is a marker is a witness or an obstruction and not a part. -/
def conditionForms : Expr → Array Form
  | .lam _ _ body _ =>
    (conjuncts body).foldl (fun all part =>
      if (part.getAppFn.constName?).any markers.contains then all
      else all ++ formsOf 0 part) #[]
  | _ => #[]

/-- Evaluate a computation of the elaborator's reduction engine on a compiled environment. -/
def reduce {α : Type} (env : Environment) (computation : MetaM α) : IO α := do
  let (result, _) ← computation.run'.toIO
    { fileName := "decision-inventory", fileMap := default } { env := env }
  return result

/-- Read one declaration of a surveyed module. A contract of a decision registry adds what
it states about its implementation. Any other written theorem adds the constants its
statement names, and checks the entries that name it as their standing theorem. A definition
or an opaque constant whose result is a verdict adds a candidate, unless it is a recursion
companion of a parent declaration. -/
def Observed.observe (observed : Observed) (env : Environment) (owner name : Name)
    (info : ConstantInfo) : IO Observed := do
  match info with
  | .thmInfo _ =>
    if registries.contains owner then
      unless info.type.getAppFn.constName? == some ``Regula.ExecutableContract do
        return observed
      let some implementation := (info.type.getAppArgs[1]?).bind (·.getAppFn.constName?)
        | throw (IO.userError s!"{name}: contract names no implementation constant")
      let some condition := info.type.getAppArgs[2]?
        | throw (IO.userError s!"{name}: contract has no condition")
      let stated := ((observed.contracts.find? implementation).getD {}).add (registered condition)
      if (kindAbout condition).isSome then
        return { observed with contracts := observed.contracts.insert implementation stated }
      let statement : Statement := ⟨name, implementation, conditionForms condition⟩
      let facts (markers : Array Name) (accepted : Bool) : Array Witness :=
        (witnessInputs markers condition).map fun inputs =>
          ⟨name, implementation, accepted, inputs.filter (own env)⟩
      return { observed with
        contracts := observed.contracts.insert implementation stated
        statements := observed.statements.push statement
        witnesses := observed.witnesses ++ facts acceptanceMarkers true ++
          facts refusalMarkers false }
    unless written env name do return observed
    let used := info.type.getUsedConstantsAsSet
    let mut standing := observed.standing
    for (definition, _, reason) in excluded do
      if reason.standing? == some name && used.contains definition then
        standing := standing.insert definition
    return { observed with
      mentioned := used.foldl (fun all constant => all.insert constant) observed.mentioned
      standing }
  | .defnInfo _ | .opaqueInfo _ =>
    let uses := (info.value?.map (·.getUsedConstants)).getD #[]
    let searches := owner != searchModule && uses.any fun constant =>
      ((env.getModuleIdxFor? constant).bind fun index =>
        env.header.moduleNames[index.toNat]?) == some searchModule
    let observed := { observed with bodies := observed.bodies.insert name uses }
    let observed := if searches then
      { observed with searchers := observed.searchers.push (name, uses) } else observed
    let some signature ← reduce env (signatureOf info.type) | return observed
    unless verdictHead signature.head do return observed
    if let some label := companion? env name info then
      return { observed with certified :=
        observed.certified.insert label (observed.certified.getD label 0 + 1) }
    let decidable := signature.head == ``Decidable
    let field := (env.getProjectionFnInfo? name).isSome
    let candidate : Candidate :=
      { name, owner, shape := signature.shape, structural := field || decidable
        decidable := decidable && !field
        generated := ← reduce env (derivedComparison env name)
        fieldDefault := ← reduce env (storedDefault env name), uses }
    return { observed with candidates := observed.candidates.push candidate }
  | _ => return observed

/-- The definitions that the implementations of the registered decisions reach through
definition bodies, the implementations included. -/
def reachable (observed : Observed) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut pending : Array Name := observed.contracts.foldl (fun all name _ => all.push name) #[]
  -- Each definition is entered at most once, so the walk ends within the number of bodies.
  for _ in [0:observed.bodies.size + pending.size + 1] do
    let mut next : Array Name := #[]
    for name in pending do
      if seen.contains name then continue
      seen := seen.insert name
      for used in (observed.bodies.find? name).getD #[] do
        unless seen.contains used do next := next.push used
    if next.isEmpty then break
    pending := next
  return seen

/-- Validate the table and apply the inventory decision to every observed definition. All
failures are reported together. `env` is the environment that holds the registries, from
which the dependencies of the witness inputs are read. -/
def check (observed : Observed) (env : Environment) : IO Unit := do
  let reached := reachable observed
  let mut failures : Array String := #[]
  let mut candidates : NameMap Candidate := {}
  let mut applied : NameSet := observed.contracts.foldl (fun all name _ => all.insert name) {}
  for candidate in observed.candidates do
    candidates := candidates.insert candidate.name candidate
    if candidate.decidable then applied := applied.insert candidate.name
  -- Each entry is valid on its own.
  let mut valid : NameSet := {}
  let mut named : NameSet := {}
  let mut counts : Std.HashMap String Nat := {}
  let mut namedBy : Std.HashMap String Nat := {}
  let mut reachedBy : Std.HashMap String Nat := {}
  for name in relied do
    unless excluded.any (·.1 == name) do
      failures := failures.push s!"{name} is in the list of reached definitions and has no entry"
  for (name, shape, reason) in excluded do
    if named.contains name then
      failures := failures.push s!"{name} has more than one exclusion entry"
      continue
    named := named.insert name
    let some candidate := candidates.find? name
      | failures := failures.push s!"exclusion entry {name} names no verdict-shaped definition"
    if candidate.structural then
      failures := failures.push s!"{name} is structural and has an exclusion entry"
    else if observed.contracts.contains name then
      failures := failures.push s!"{name} has a contract and an exclusion entry"
    else if shape != candidate.shape then
      failures := failures.push
        s!"{name} is excluded as {repr shape} but its type is {repr candidate.shape}"
    else
      let evidence : Evidence :=
        { mentioned := observed.mentioned.contains name
          applies := candidate.uses.any applied.contains
          searching := candidate.owner == searchModule &&
            observed.searchers.all fun (_, uses) =>
              !uses.contains name || uses.any applied.contains
          generated := candidate.generated
          fieldDefault := candidate.fieldDefault
          proofLibrary := (`AcornVerif).isPrefixOf candidate.owner
          standing := observed.standing.contains name
          reached := reached.contains name
          relied := relied.contains name }
      if reason.supported evidence then
        valid := valid.insert name
        counts := counts.insert reason.label (counts.getD reason.label 0 + 1)
        if evidence.mentioned then
          namedBy := namedBy.insert reason.label (namedBy.getD reason.label 0 + 1)
        if evidence.reached then
          reachedBy := reachedBy.insert reason.label (reachedBy.getD reason.label 0 + 1)
      else
        failures := failures.push
          s!"{name}: the facts do not support its reason {repr reason} ({repr evidence})"
  -- Each definition is in exactly one class.
  let mut structural := 0
  let mut contracts := 0
  let mut decided := 0
  for candidate in observed.candidates do
    let classes : Classes :=
      ⟨candidate.structural, observed.contracts.contains candidate.name,
        valid.contains candidate.name⟩
    if classified classes then
      if classes.structural then structural := structural + 1
      if classes.contract then
        contracts := contracts + 1
        if ((observed.contracts.find? candidate.name).any (·.kind)) then decided := decided + 1
    else if !named.contains candidate.name then
      failures := failures.push (s!"{candidate.name} has no contract and no exclusion entry " ++
        s!"(its type is {repr candidate.shape})")
    else if classes.structural && classes.contract then
      failures := failures.push s!"{candidate.name} is structural and has a contract"
  -- A marked witness counts only when no input of it depends on the decision function. This
  -- is the one place that examines the input of a witness.
  let depends := closure env (observed.witnesses.foldl (fun all witness =>
    all ++ witness.inputs) #[])
  let mut functions := observed.contracts
  for witness in observed.witnesses do
    if reaches depends.find? witness.implementation witness.inputs (depends.size + 1) then
      failures := failures.push (s!"{witness.contract}: an input of a witness depends on the " ++
        s!"decision function {witness.implementation}, or on a constant that the audit did " ++
        "not read")
    else
      let stated := (functions.find? witness.implementation).getD {}
      functions := functions.insert witness.implementation
        (if witness.accepted then { stated with accepted := true }
          else { stated with refused := true })
  -- Each decision function has a two-way kind, or a marked accepted input or a proof that
  -- none exists, and a marked refused input or a proof that none exists.
  let stated := functions.foldl (fun all name stated => all.push (name, stated)) #[]
  for (name, stated) in stated do
    unless stated.accepted || stated.neverAccepted do
      failures := failures.push (s!"{name}: no contract is a two-way kind, carries a marked " ++
        "accepted input or proves that every input is refused")
    unless stated.refused || stated.neverRefused do
      failures := failures.push (s!"{name}: no contract is a two-way kind, carries a marked " ++
        "refused input or proves that every input is accepted")
  unless failures.isEmpty do
    for failure in failures do IO.eprintln s!"decision inventory: {failure}"
    throw (IO.userError s!"{failures.size} decision inventory failures")
  let all := Reason.plainLabels ++ [Reason.namedLabel]
  let listed (table : Std.HashMap String Nat) : String :=
    ", ".intercalate ((all.filter fun label => table.getD label 0 != 0).map fun label =>
      s!"{label} {table.getD label 0}")
  let total (table : Std.HashMap String Nat) : Nat := (all.map fun label => table.getD label 0).sum
  IO.println (s!"decisions: {observed.candidates.size} verdict-shaped definitions: " ++
    s!"{structural} structural, {contracts} with a contract ({decided} with a decision " ++
    s!"kind, {contracts - decided} with a requirement that the Regula audit does not check " ++
    "for witnesses or independence), " ++
    s!"{total counts} excluded with a computed reason ({listed counts}); " ++
    s!"a written theorem names {total namedBy} of the excluded ({listed namedBy}); " ++
    s!"a registered decision reaches {total reachedBy} of the excluded, and no theorem names " ++
    s!"them ({listed reachedBy}); " ++
    s!"recursion companions outside the domain: {observed.certified.toList}")
  -- Witnesses and obstructions.
  let names (select : Registered → Bool) : List String :=
    ((stated.filter fun (_, stated) => select stated).map (·.1.toString)).qsort (· < ·) |>.toList
  let empty := names fun stated => !stated.accepted
  let total := names fun stated => !stated.refused
  let fixed := (stated.filter fun (name, _) =>
    (observed.contracts.find? name).any fun declared => declared.accepted && declared.refused).size
  IO.println (s!"decision witnesses: {stated.size} decision functions with a contract; " ++
    s!"{fixed} with a two-way kind, which fixes the verdict at every input; " ++
    s!"{observed.witnesses.size} marked inputs examined, none depends on its function; " ++
    s!"{empty.length} functions with no accepted input, each with a proof that every input " ++
    s!"is refused: {empty}; " ++
    s!"{total.length} with no refused input, each with a proof that every input is " ++
    s!"accepted: {total}")
  -- The form of each part of each statement with no kind.
  let ordered := observed.statements.qsort fun left right =>
    left.contract.toString < right.contract.toString
  let exact (form : Form) : Bool := form != .unclassified
  for statement in ordered do
    let forms := if statement.forms.isEmpty then "markers only"
      else "; ".intercalate (statement.forms.map Form.label).toList
    IO.println s!"decision statement {statement.contract} of {statement.implementation}: {forms}"
  let count (select : Array Form → Bool) : Nat :=
    (observed.statements.filter fun statement => select statement.forms).size
  IO.println (s!"decision statements with no kind: {observed.statements.size}; " ++
    s!"{count fun forms => !forms.isEmpty && forms.all exact} in which each part has an exact " ++
    s!"form, {count fun forms => forms.any exact && !forms.all exact} with an exact part and " ++
    s!"a part that is not classified, {count fun forms => !forms.isEmpty && !forms.any exact} " ++
    s!"with no exact part and {count Array.isEmpty} with markers only")

/-- The cases that a name, a flag or a count of written binders would decide wrongly, as
written declarations of `AcornTools.DecisionInventoryControls`. The audit refuses to run
unless no companion relationship removes the written definition named like a matcher, the
opaque constant, the unsafe definition or the two field defaults that are functions; the
written theorem below a constructor counts as written; the handwritten comparison of a
declared instance is not `derived`; and neither field default that is a function is a stored
default, the one behind a reducible definition included. -/
def controls (env : Environment) : IO Unit := do
  let root := `AcornDecisionInventory.Control
  let matcher := root ++ `T.match_37
  let below := root ++ `T.a.refused
  let comparison := root ++ `instBEqT.beq
  let sealed := root ++ `sealed
  let gate := root ++ `gate
  let guard := Lean.mkDefaultFnOfProjFn (root ++ `Guard.accepts)
  let veiled := Lean.mkDefaultFnOfProjFn (root ++ `Veiled.accepts)
  for name in #[matcher, comparison, sealed, gate, guard, veiled] do
    let some info := env.find? name
      | throw (IO.userError s!"decision inventory control {name} is missing")
    let some signature ← reduce env (signatureOf info.type)
      | throw (IO.userError s!"decision inventory control {name} has no signature")
    unless verdictHead signature.head do
      throw (IO.userError s!"decision inventory: the written control {name} is not verdict-shaped")
    if let some label := companion? env name info then
      throw (IO.userError s!"decision inventory: the written control {name} left as {label}")
  unless env.contains below && written env below do
    throw (IO.userError "decision inventory: a written theorem below a constructor is not counted")
  if ← reduce env (derivedComparison env comparison) then
    throw (IO.userError "decision inventory: a handwritten comparison is accepted as derived")
  for default in #[guard, veiled] do
    if ← reduce env (storedDefault env default) then
      throw (IO.userError
        s!"decision inventory: the field default {default} is a function and is a stored value")
  let marker := #[root ++ `Accepts]
  let condition (name : Name) : IO Expr := do
    let some value := (env.find? (root ++ name)).bind (·.value?)
      | throw (IO.userError s!"decision inventory control {root ++ name} is missing")
    return value
  unless (witnessInputs marker (← condition `closedFact)).size == 1 do
    throw (IO.userError "decision inventory: a closed witness at the top level is not counted")
  for name in #[`hypothetical, `quantified, `unconditional, `foreign, `selfBuilt] do
    unless (witnessInputs marker (← condition name)).isEmpty do
      throw (IO.userError s!"decision inventory: the marker of control {name} is counted")
  -- An input that depends on the decided function is refused: through a definition, through
  -- the value of an opaque constant, through the value of a theorem and through the type of a
  -- constructor. A closed input is not refused.
  let uses (name : Name) : Option (Array Name) :=
    (env.find? name).map fun info => (dependencies info).filter (own env)
  let dependent (name : Name) : IO Bool := do
    match witnessInputs marker (← condition name) with
    | #[inputs] =>
      return reaches uses (root ++ `T.match_37) (inputs.filter (own env)) 1000
    | _ => throw (IO.userError s!"decision inventory: the control {name} has no witness")
  for name in #[`viaDefinition, `viaOpaque, `viaTheorem, `viaStructure] do
    unless ← dependent name do
      throw (IO.userError s!"decision inventory: the dependent input of control {name} is accepted")
  if ← dependent `closedFact then
    throw (IO.userError "decision inventory: a closed input is refused as a dependent one")
  unless reaches (fun _ => none) (root ++ `T.match_37) #[root ++ `chosen] 1000 do
    throw (IO.userError "decision inventory: a constant that the audit did not read is accepted")
  -- A proof that every input is accepted states the fact at exactly the quantified inputs.
  unless everyInput marker ((← condition `everyAccepted).bindingBody!) do
    throw (IO.userError "decision inventory: a statement for every input is not counted")
  for name in #[`someAccepted, `guardedAccepted] do
    if everyInput marker ((← condition name).bindingBody!) then
      throw (IO.userError s!"decision inventory: the control {name} counts as every input")
  -- A two-way kind about the bound function counts for both sides. A one-way kind and a kind
  -- about another function count for no side.
  let twoWay := registered (← condition `ownKind)
  unless twoWay.kind && twoWay.accepted && twoWay.refused do
    throw (IO.userError "decision inventory: a two-way kind about the bound function is not counted")
  let oneWay := registered (← condition `soundKind)
  unless oneWay.kind && !oneWay.accepted && !oneWay.refused do
    throw (IO.userError "decision inventory: a one-way kind counts as a witness")
  if (kindAbout (← condition `foreignKind)).isSome then
    throw (IO.userError "decision inventory: a kind about another function is counted")
  -- Only the two exact shapes have a strong form.
  for (name, expected) in
      [(`exact, #[Form.verdict]), (`total, #[.result]), (`below, #[.verdict]),
        (`guarded, #[.unclassified]), (`veiled, #[.unclassified]), (`wrapped, #[.unclassified]),
        (`mixed, #[.verdict, .unclassified]), (`falseGuard, #[.unclassified]),
        (`emptyDomain, #[.unclassified]), (`hiddenDomain, #[.unclassified]),
        (`extraInput, #[.unclassified]), (`markedBelow, #[.unclassified])] do
    unless conditionForms (← condition name) == expected do
      throw (IO.userError s!"decision inventory: the form of the control {name} is wrong")

end AcornDecisionInventory
