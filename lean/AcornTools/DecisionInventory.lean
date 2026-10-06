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

## What is computed and what is a judgment

The domain, the three classes, the shape and five of the eight reasons are computed from the
compiled environment. `Reason` states the fact behind each computed reason; an entry whose
fact is false fails verification.

Three reasons are judgments: `transition`, `selection` and `predicate` say that a definition
is not a decision although theorems mention it. The judgment is that its result is not a
verdict a claim relies on: the caller that reads it takes the next state, a selected value
or a branch of a transition from it, and no input from outside the admitted state is accepted
or refused by it. Each such entry names a standing theorem, and the audit checks that the
theorem is a written theorem of a maintained module whose statement mentions the definition.
A definition whose theorems state which inputs it accepts or refuses is registered with a
contract instead.

The test for the judgment is who reads the result, and for what. A definition is a decision,
and is never in the judgment class, when a caller refuses, suppresses or admits on its
result, so that an external action, a published value or a stored record depends on it, or
when a caller reads the result to accept or refuse something that came from outside the
admitted state. It is not a decision when the transition that called it reads the result as
its next state, as a value to use, or as a property of state that was already admitted, to
choose which of its own branches runs, and passes a refusal on as its own. The borderline
cases, each kept as a judgment for the reason given:

* `Features.Lifecycle.eligible` and `mature` are properties of a unit that the selection
  `Features.Lifecycle.candidate` reads; the contract of `candidate` states when it selects.
* `Host.terrain` and `Host.World.tileKind` compute a tile and refuse on signed overflow. The
  checks that read a tile to accept or refuse a move or a certificate (`Host.World.enterable`,
  `Host.impassable`, `Host.walkableTile`) have contracts.
* `Host.Action.direction` is a total table that the transition `Host.performAction` reads.

A use during the compilation of a published schema counts as an admission, and a contract
on a caller is no reason to exclude the function that the caller branches on.

`judged_count` and `computed_count` state how many entries are judgments and how many carry
a computed reason. A new judgment changes the first number and needs its standing theorem.

## The domain

The domain holds every constant of the surveyed modules that can carry an executable body,
a definition or an opaque constant, private ones included, whose type is verdict-shaped. A
field default and an instance are such constants. A constant leaves the domain only by a
certificate that the environment gives for that constant (`certificate?`): the matcher
data, the auxiliary-recursor data, the no-confusion data, the kernel's partial or unsafe flag of a
recursion companion, and the equation data of the structural and well-founded recursion
compilers for the companions they generate. A name alone decides nothing, and neither does
the source range that Lean records for a declaration: a range is metadata, a written field
default has none, and a derived comparison has one. A constant with no certificate is
treated as written, and it needs a contract or a valid entry. The audit prints how many
constants left by each certificate. `controls` checks five written declarations that a name
or a range would get wrong.

This is a check that every such definition has been classified and that each computed fact
holds. Whether a judgment is right is review.
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

/-- Why a verdict-shaped definition carries no contract. The first five are computed: the
audit checks the stated fact. The last three are judgments, each with a standing theorem. -/
inductive Reason where
  /-- Computed: no written theorem of the maintained libraries names the definition in its
  statement. This is the absence of a direct reference and nothing more: a theorem about a
  caller can still imply a property of the definition. A contract of a decision registry and
  a proof field of a structure are not counted: the first is a registration, the second
  states what a value of that structure carries. -/
  | unproved
  /-- Computed: the fact of `unproved`, and the body applies a definition that has a
  contract or a `Decidable` result. The contracts of the decisions it applies stand. -/
  | composed
  /-- Computed: the fact of `unproved`, and the definition belongs to the certificate search
  module. A registered checker decides every proposal. -/
  | proposal
  /-- Computed: the definition is the comparison of a registered `BEq` instance of a type of
  the same module, and the recorded ranges of both lie inside the declaration of that type,
  where a `deriving` clause puts what it generates. -/
  | derived
  /-- Computed: the definition is the default value of a structure field and takes no
  argument beyond the parameters of the structure, so it is a stored value. -/
  | default
  /-- Computed: the definition belongs to the proof library, which has no executable. Its
  theorems relate it to the executing definitions, and no claim rests on running it. -/
  | model
  /-- Judgment: the result is the outcome of a state transition or of a computation step,
  and a refusal reports that the step did not happen. `standing` is a theorem about it. -/
  | transition (standing : Name)
  /-- Judgment: the optional result is a selection, a lookup or a derived value, and an
  absent result reports that there is nothing to return. `standing` is a theorem about it. -/
  | selection (standing : Name)
  /-- Judgment: a Boolean property of state the library has already admitted, which selects
  a branch of a transition. `standing` is a theorem about it. -/
  | predicate (standing : Name)
  deriving DecidableEq, Repr

/-- The standing theorem of a judgment. -/
def Reason.standing? : Reason → Option Name
  | .transition standing | .selection standing | .predicate standing => some standing
  | _ => none

/-- The name of a reason, without its standing theorem. -/
def Reason.label : Reason → String
  | .unproved => "unproved" | .composed => "composed" | .proposal => "proposal"
  | .derived => "derived" | .default => "default" | .model => "model"
  | .transition _ => "transition"
  | .selection _ => "selection" | .predicate _ => "predicate"

/-- The names of the computed reasons. -/
def Reason.computedLabels : List String :=
  ["unproved", "composed", "proposal", "derived", "default", "model"]

/-- The names of the reasons that are judgments. -/
def Reason.judgmentLabels : List String := ["transition", "selection", "predicate"]

/-- The two lists hold every reason, each in the list for what it is: a reason with a
standing theorem is a judgment, and every other reason is computed. -/
theorem Reason.label_listed (reason : Reason) :
    (reason.standing?.isNone → reason.label ∈ Reason.computedLabels) ∧
      (reason.standing?.isSome → reason.label ∈ Reason.judgmentLabels) := by
  cases reason <;> simp [Reason.label, Reason.standing?, Reason.computedLabels,
    Reason.judgmentLabels]

/-- The facts the audit computes about one excluded definition. -/
structure Evidence where
  /-- A written theorem of the maintained libraries, outside the decision registries,
  mentions the definition in its statement. -/
  mentioned : Bool
  /-- The body applies a definition that has a contract or a `Decidable` result. -/
  applies : Bool
  /-- The definition belongs to the certificate search module. -/
  searching : Bool
  /-- The definition is the comparison of a derived instance. -/
  generated : Bool
  /-- The definition is the default of a structure field with no argument of its own. -/
  fieldDefault : Bool
  /-- The definition belongs to the proof library. -/
  proofLibrary : Bool
  /-- The entry's standing theorem is such a written theorem and mentions the definition. -/
  standing : Bool
  deriving DecidableEq, Repr

/-- Whether the computed facts support a reason. -/
def Reason.supported : Reason → Evidence → Bool
  | .unproved, evidence => !evidence.mentioned
  | .composed, evidence => !evidence.mentioned && evidence.applies
  | .proposal, evidence => !evidence.mentioned && evidence.searching
  | .derived, evidence => evidence.generated
  | .default, evidence => evidence.fieldDefault
  | .model, evidence => evidence.proofLibrary
  | .transition _, evidence | .selection _, evidence | .predicate _, evidence =>
    evidence.standing

/-- A reason with no standing theorem is supported by computed facts alone. -/
theorem Reason.supported_computed (reason : Reason) (left right : Evidence)
    (computed : reason.standing? = none) (mentioned : left.mentioned = right.mentioned)
    (applies : left.applies = right.applies) (searching : left.searching = right.searching)
    (generated : left.generated = right.generated)
    (fieldDefault : left.fieldDefault = right.fieldDefault)
    (proofLibrary : left.proofLibrary = right.proofLibrary) :
    reason.supported left = reason.supported right := by
  cases reason <;> simp_all [Reason.supported, Reason.standing?]

/-- A "no theorem" reason is refused for a definition that a theorem mentions. -/
theorem Reason.unproved_refused (reason : Reason) (evidence : Evidence)
    (mentioned : evidence.mentioned = true)
    (unproved : reason = .unproved ∨ reason = .composed ∨ reason = .proposal) :
    reason.supported evidence = false := by
  rcases unproved with rfl | rfl | rfl <;> simp [Reason.supported, mentioned]

/-- A judgment is supported exactly when its standing theorem is checked. -/
theorem Reason.supported_judgment (reason : Reason) (evidence : Evidence) (standing : Name)
    (judged : reason.standing? = some standing) :
    reason.supported evidence = evidence.standing := by
  cases reason <;> simp_all [Reason.supported, Reason.standing?]

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
  (`Acorn.Features.Assignment.feature, .dependent, .unproved),
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
  (`Acorn.SwiftTd.nextReady, .dependent,
    .transition `Acorn.Features.Managed.apply._proof_1),
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
  (`Acorn.Agreement.Total.observe, .dependent, .transition `Acorn.Agreement.Total.observe_exact),
  (`Acorn.Features.ExploratoryRun.serve, .dependent,
    .transition `Acorn.Features.ExploratoryRun.serve_exact),
  (`Acorn.Handcrafted.Agent.input, .dependent, .transition `AcornVerif.CurrentAgent.edge_contract),
  (`Acorn.Handcrafted.Agent.runPrefix, .dependent,
    .transition `Acorn.Handcrafted.Agent.clear_suffix),
  (`Acorn.Handcrafted.AgentConstruction.execute, .dependent,
    .transition `AcornVerif.CurrentAgent.native_prefix),
  (`Acorn.Handcrafted.TemporalControl.atBoundary, .dependent,
    .transition `Acorn.Handcrafted.TemporalControl.atBoundary_assigns),
  (`Acorn.Handcrafted.TemporalControl.dispatchMeta, .dependent,
    .transition `Acorn.Handcrafted.TemporalControl.dispatchMeta_eq),
  (`Acorn.Handcrafted.TemporalControl.select, .dependent,
    .transition `AcornVerif.CurrentTemporal.step_executing),
  (`Acorn.Handcrafted.TemporalControl.selectWithOperations, .dependent,
    .transition `Acorn.Handcrafted.TemporalControl.primitive_undrawn),
  (`Acorn.Handcrafted.TemporalControl.serve, .dependent,
    .transition `Acorn.Handcrafted.TemporalControl.select_drawn),
  (`Acorn.Handcrafted.TemporalControl.step, .dependent,
    .transition `Acorn.Handcrafted.TemporalControl.step_episodes),
  (`Acorn.Host.AnsiState.tick, .dependent, .transition `Acorn.Host.AnsiState.tick_observation),
  (`Acorn.Host.Attempt.finish, .dependent, .transition `Acorn.Host.Attempt.finish_position),
  (`Acorn.Host.Attempt.sense, .dependent, .transition `AcornVerif.CurrentRunner.sense_none),
  (`Acorn.Host.Attempt.tick, .dependent, .transition `Acorn.Host.Attempt.tick_finished),
  (`Acorn.Host.BaselineAttempt.tick, .dependent,
    .transition `AcornVerif.CurrentRunner.idle_corresponds),
  (`Acorn.Host.OwnedStep.environment, .dependent,
    .transition `Acorn.Host.SelectedStep.owned_commit),
  (`Acorn.Host.PreparedStep.commit, .dependent, .transition `AcornVerif.CurrentRunner.commit_clock),
  (`Acorn.Host.PreparedStep.environment, .dependent,
    .transition `Acorn.Host.SelectedStep.owned_commit),
  (`Acorn.Host.World.advanceActions, .dependent,
    .transition `Acorn.Host.World.advanceActions_clock),
  (`Acorn.Host.World.initial, .dependent, .transition `Acorn.Host.World.initial_fields),
  (`Acorn.Host.World.observe, .dependent, .transition `Acorn.Host.World.observe_task),
  (`Acorn.Host.World.step, .dependent, .transition `Acorn.Host.World.step_clock),
  (`Acorn.Host.World.tileKind, .dependent,
    .transition `AcornVerif.CurrentCertificates.stance_harvest),
  (`Acorn.Host.considerSpawn, .dependent,
    .transition `AcornVerif.CurrentSpawn.considerSpawn_contract),
  (`Acorn.Host.countKindNear, .dependent, .transition `AcornVerif.CurrentSpawn.countKindNear_eq),
  (`Acorn.Host.payAndAct, .dependent, .transition `AcornVerif.CurrentStep.payAndAct_outcome),
  (`Acorn.Host.performAction, .dependent, .transition `AcornVerif.CurrentCertificates.perform_move),
  (`Acorn.Host.runBaselineCampaign, .dependent,
    .transition `AcornVerif.CurrentRunner.baseline_campaign_finishes),
  (`Acorn.Host.runRandomBaseline, .fixed, .transition `AcornVerif.CurrentRunner.baseline_finishes),
  (`Acorn.Host.selectSpawn, .dependent, .transition `AcornVerif.CurrentSpawn.initial_spawn),
  (`Acorn.Host.terrain, .fixed, .transition `AcornVerif.CurrentCertificates.stance_yield),
  (`Acorn.Features.Assignment.identity, .dependent,
    .selection `Acorn.Features.Assignment.Distinct.mono),
  (`Acorn.Features.Lifecycle.prefer, .dependent, .selection `Acorn.Features.Lifecycle.fold_scanned),
  (`Acorn.Features.Occupancy.executing, .dependent,
    .selection `Acorn.Features.Occupancy.afterOption_executing),
  (`Acorn.Features.RankedFeatures.position, .dependent,
    .selection `Acorn.Features.RankedFeatures.position_complete),
  (`Acorn.Features.TemporalDecision.episodeEnd, .dependent,
    .selection `Acorn.Handcrafted.TemporalControl.finish_options),
  (`Acorn.Features.best, .dependent, .selection `Acorn.Features.best_spec),
  (`Acorn.Features.kept, .dependent, .selection `Acorn.Features.entrants_le_open),
  (`Acorn.Handcrafted.TemporalControl.activeSlot, .dependent,
    .selection `Acorn.Handcrafted.TemporalControl.boundary_episodes),
  (`Acorn.Handcrafted.TemporalControl.takeoverValue, .dependent,
    .selection `AcornVerif.CurrentTemporal.takeover_none),
  (`Acorn.Handcrafted.skillOfMeta, .fixed,
    .selection `Acorn.Handcrafted.TemporalControl.dispatchMeta_eq),
  (`Acorn.Host.Action.direction, .fixed, .selection `AcornVerif.CurrentCertificates.perform_move),
  (`Acorn.Features.Assignment.potential, .dependent,
    .predicate `AcornVerif.CurrentTemporal.learned_potential),
  (`Acorn.Features.Ensemble.holds, .dependent,
    .predicate `Acorn.Features.Ensemble.releaseAll_unheld),
  (`Acorn.Features.Interface.reserved, .fixed,
    .predicate `Acorn.Handcrafted.Grid.sensorWords_clear),
  (`Acorn.Features.Lifecycle.eligible, .dependent,
    .predicate `Acorn.Features.Lifecycle.candidate_eligible),
  (`Acorn.Features.Lifecycle.mature, .dependent, .predicate `AcornVerif.Retirement.run_immature),
  (`Acorn.Features.Occupancy.free, .dependent,
    .predicate `Acorn.Features.FeatureRuntime.retire_occupied),
  (`Acorn.Features.OptionActivation.learning, .dependent,
    .predicate `Acorn.Features.Skill.stepTemporal_eq),
  (`Acorn.Features.TemporalDecision.own, .dependent,
    .predicate `Acorn.Handcrafted.TemporalControl.finish_credit),
  (`Acorn.Handcrafted.FeatureProfile.ranksSubtasks, .fixed,
    .predicate `Acorn.Handcrafted.TemporalControl.atBoundary_assigns),
  (`Acorn.Handcrafted.FeatureProfile.usesHierarchy, .fixed,
    .predicate `Acorn.Handcrafted.TemporalControl.finish_eq),
  (`Acorn.Handcrafted.askedBy, .dependent,
    .predicate `Acorn.Handcrafted.TemporalControl.finish_skill)
]

/-- The entries that are judgments: each names a standing theorem. -/
theorem judged_count : (excluded.filter fun entry => entry.2.2.standing?.isSome).size = 55 := by
  decide +kernel

/-- The entries whose reason is a computed fact. -/
theorem computed_count : (excluded.filter fun entry => entry.2.2.standing?.isNone).size = 207 := by
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

/-- What the contracts of the registries state about one decision function. -/
structure Registered where
  /-- One of its contracts is a decision kind. -/
  kind : Bool := false
  /-- One of its contracts carries an input that the function accepts. -/
  accepted : Bool := false
  /-- One of its contracts carries an input that the function refuses. -/
  refused : Bool := false

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

/-- Join what two contracts state about one function. -/
def Registered.add (left right : Registered) : Registered :=
  ⟨left.kind || right.kind, left.accepted || right.accepted, left.refused || right.refused⟩

/-- Join the observations of two environments. -/
def Observed.add (left right : Observed) : Observed :=
  { candidates := left.candidates ++ right.candidates
    contracts := right.contracts.foldl (fun all name stated =>
      all.insert name (((all.find? name).getD {}).add stated)) left.contracts
    mentioned := right.mentioned.foldl (fun all name => all.insert name) left.mentioned
    standing := right.standing.foldl (fun all name => all.insert name) left.standing
    certified := right.certified.fold (fun all label count =>
      all.insert label (all.getD label 0 + count)) left.certified
    searchers := left.searchers ++ right.searchers }

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

/-- Whether Lean generated a theorem, by a certificate of the environment: a proof field
of a structure, an equation or unfolding theorem under a reserved name, or the injectivity
or size theorem that Lean names for a recorded constructor. Every other theorem is written. -/
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

/-- Whether a requirement with no kind carries a witness with one of the given markers: a
conjunct at the top level of the condition whose predicate is a standard one and whose
result is an application of the implementation that the condition binds. Such a conjunct is
below no quantifier and no hypothesis, so it is a proved statement about one closed input. -/
def witnessed (markers : Array Name) : Expr → Bool
  | .lam _ _ body _ =>
    (conjuncts body).any fun fact =>
      (fact.getAppFn.constName?).any markers.contains &&
        (match fact.getAppArgs with
          | #[_, predicate, result] => standardAccepts predicate && result.getAppFn == .bvar 0
          | _ => false)
  | _ => false

/-- What one contract condition states: its kind, and the witnesses it carries. A two-way
kind carries both witnesses in its type, a sound kind the accepted one and a complete kind
the refused one. -/
def registered (condition : Expr) : Registered :=
  match (conditionBody condition).getAppFn.constName? with
  | some ``Regula.Decides => ⟨true, true, true⟩
  | some ``Regula.DecidesSoundly => ⟨true, true, false⟩
  | some ``Regula.DecidesCompletely => ⟨true, false, true⟩
  | _ => ⟨false, witnessed acceptanceMarkers condition, witnessed refusalMarkers condition⟩

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
      return { observed with contracts := observed.contracts.insert implementation stated }
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

/-- Validate the table and apply the inventory decision to every observed definition. All
failures are reported together. -/
def check (observed : Observed) : IO Unit := do
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
          standing := observed.standing.contains name }
      if reason.supported evidence then
        valid := valid.insert name
        counts := counts.insert reason.label (counts.getD reason.label 0 + 1)
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
  unless failures.isEmpty do
    for failure in failures do IO.eprintln s!"decision inventory: {failure}"
    throw (IO.userError s!"{failures.size} decision inventory failures")
  let count (label : String) : Nat := counts.getD label 0
  let reasons (labels : List String) : String :=
    ", ".intercalate (labels.map fun label => s!"{label} {count label}")
  let computed := (Reason.computedLabels.map count).sum
  let judged := (Reason.judgmentLabels.map count).sum
  IO.println (s!"decisions: {observed.candidates.size} verdict-shaped definitions: " ++
    s!"{structural} structural, {contracts} with a contract ({decided} with a decision " ++
    s!"kind, {contracts - decided} with a requirement that the Regula audit does not check " ++
    "for witnesses or independence), " ++
    s!"{computed} excluded by a computed reason ({reasons Reason.computedLabels}), " ++
    s!"{judged} excluded by judgment with a standing theorem " ++
    s!"({reasons Reason.judgmentLabels}); " ++
    s!"recursion companions outside the domain: {observed.certified.toList}")
  -- The decision functions whose contracts carry no accepted or no refused input.
  let stated := observed.contracts.foldl (fun all name stated => all.push (name, stated)) #[]
  let lacking (select : Registered → Bool) : List String :=
    ((stated.filter fun (_, stated) => !select stated).map (·.1.toString)).qsort (· < ·) |>.toList
  let unaccepted := lacking (·.accepted)
  let unrefused := lacking (·.refused)
  IO.println (s!"decision witnesses: {stated.size} decision functions with a contract; " ++
    s!"{unaccepted.length} with no accepted input in a contract: {unaccepted}; " ++
    s!"{unrefused.length} with no refused input in a contract: {unrefused}")

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
  unless witnessed marker (← condition `closedFact) do
    throw (IO.userError "decision inventory: a closed witness at the top level is not counted")
  for name in #[`hypothetical, `quantified, `unconditional, `foreign] do
    if witnessed marker (← condition name) then
      throw (IO.userError s!"decision inventory: the marker of control {name} is counted")

end AcornDecisionInventory
