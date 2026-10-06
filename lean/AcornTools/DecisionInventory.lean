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
and is never in the judgment class, when a caller reads its result to accept or refuse
something that came from outside the admitted state (bytes, text, raw words, a certificate, a
candidate value), or when a printed or stored claim rests on the result itself, as with goal
completion and a certificate verdict. It is not a decision when the transition that called it
reads the result as its next state, as a value to use, or as a property of state that was
already admitted, to choose which of its own branches runs. The borderline cases, each kept as
a judgment for the reason given:

* `Host.Attempt.finished` ends an attempt. The outcome that is recorded is the completion
  flag `Host.World.goalSatisfied`, which has a contract; `finished` only stops the stepping.
* `Host.BoundaryDecision.closing` and `Host.WritableCheckpoint.dueAt` schedule a checkpoint
  write. No claim rests on the schedule: what is written is admitted again when it is loaded.
* `Host.Inventory.owns` reads one stored flag. The craft-goal verdict is
  `Host.TaskObservation.satisfied`, whose contract states ownership as its specification.
* `Features.Lifecycle.eligible` and `mature` are properties of a unit that the selection
  `Features.Lifecycle.candidate` reads; the contract of `candidate` states when it selects.
* `Agreement.Aggregate.ratio`, `Agreement.Channel.ratio` and `Agreement.aggregateAll` return
  a score or its absence. The verdict that a sample is invalid is made when the channel
  settles, by `Agreement.Ratio.admit` and `Agreement.precision`, which have contracts.
* `Host.terrain` and `Host.World.tileKind` compute a tile and refuse on signed overflow. The
  checks that read a tile to accept or refuse a move or a certificate (`Host.World.enterable`,
  `Host.impassable`, `Host.walkableTile`) have contracts.

`judged_count` and `computed_count` state how many entries are judgments and how many carry
a computed reason. A new judgment changes the first number and needs its standing theorem.

## The domain

The domain holds every definition of the surveyed modules, private ones included, except the
auxiliaries of the elaborator and the compiler. `auxiliary` is the filter: it removes a name
exactly when a component of its user-facing name is numeric, begins with an underscore, or
is `match_`, `proof_` or `eq_` followed by digits (`auxiliary_iff`). A source definition has
no such component, because Lean refuses a written name with a leading underscore and
reserves the three numbered forms. The audit also requires a declaration at or above the
part of a removed name before its first such component, so the filter removes only an
auxiliary of an existing declaration, and it prints how many definitions it removed.

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
  /-- Computed: no written theorem of the maintained libraries mentions the definition in
  its statement, so nothing is proved about it that a contract could state. A contract of a
  decision registry and a proof field of a structure are not counted: the first is a
  registration, the second states what a value of that structure carries. -/
  | unproved
  /-- Computed: the fact of `unproved`, and the body applies a definition that has a
  contract or a `Decidable` result. The contracts of the decisions it applies stand. -/
  | composed
  /-- Computed: the fact of `unproved`, and the definition belongs to the certificate search
  module. A registered checker decides every proposal. -/
  | proposal
  /-- Computed: the definition is the comparison of an instance that a `deriving` clause
  generated. -/
  | derived
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
  | .derived => "derived" | .model => "model" | .transition _ => "transition"
  | .selection _ => "selection" | .predicate _ => "predicate"

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
  | .model, evidence => evidence.proofLibrary
  | .transition _, evidence | .selection _, evidence | .predicate _, evidence =>
    evidence.standing

/-- A reason with no standing theorem is supported by computed facts alone. -/
theorem Reason.supported_computed (reason : Reason) (left right : Evidence)
    (computed : reason.standing? = none) (mentioned : left.mentioned = right.mentioned)
    (applies : left.applies = right.applies) (searching : left.searching = right.searching)
    (generated : left.generated = right.generated)
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

/-- A name component that the elaborator or the compiler generates: it begins with an
underscore, or it is `match_`, `proof_` or `eq_` followed by digits. -/
def auxiliaryComponent (component : String) : Bool :=
  component.startsWith "_" || #["match_", "proof_", "eq_"].any fun lead =>
    component.startsWith lead && lead.length < component.length &&
      (component.drop lead.length).all Char.isDigit

/-- The domain filter, on a user-facing name: some component is numeric or is an auxiliary
component. -/
def auxiliary : Name → Bool
  | .anonymous => false
  | .num _ _ => true
  | .str parent component => auxiliaryComponent component || auxiliary parent

/-- The filter removes a name exactly when one of its components is numeric or auxiliary. -/
theorem auxiliary_iff (name : Name) : auxiliary name = true ↔
    ∃ component ∈ name.components, match component with
      | .num _ _ => True
      | .str _ text => auxiliaryComponent text = true
      | .anonymous => False := by
  induction name with
  | anonymous => simp [auxiliary, Name.components, Name.componentsRev]
  | str parent text ih =>
    simp only [auxiliary, Bool.or_eq_true, ih, Name.components, Name.componentsRev,
      List.reverse_cons, List.mem_append, List.mem_singleton]
    constructor
    · rintro (own | ⟨component, member, holds⟩)
      · exact ⟨.str .anonymous text, .inr rfl, own⟩
      · exact ⟨component, .inl member, holds⟩
    · rintro ⟨component, member | rfl, holds⟩
      · exact .inr ⟨component, member, holds⟩
      · exact .inl holds
  | num parent index ih =>
    simp only [auxiliary, Name.components, Name.componentsRev, List.reverse_cons,
      List.mem_append, List.mem_singleton, true_iff]
    exact ⟨.num .anonymous index, .inr rfl, trivial⟩

/-- The longest prefix of a user-facing name that the filter keeps. -/
def sourceParent : Name → Name
  | .anonymous => .anonymous
  | .num parent _ => sourceParent parent
  | .str parent component =>
    if auxiliary (.str parent component) then sourceParent parent else .str parent component

/-- The compiled name of a private definition of a module. -/
def hidden (module user : Name) : Name := mkPrivateNameCore module user

/-- Every verdict-shaped definition of the claimed libraries that is neither structural nor
the implementation of a contract, with the shape of its type and its reason. -/
def excluded : Array (Name × Shape × Reason) := #[
  (`Acorn.AgentDriver.dispatch, .fixed, .unproved),
  (`Acorn.Agreement.Total.ratio, .dependent, .unproved),
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
  (`Acorn.Host.Viewer.BrowserConversion.number, .fixed, .unproved),
  (`Acorn.Host.Viewer.BrowserConversion.numbers, .fixed, .unproved),
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
  (`Acorn.Host.Viewer.browserIndexBound, .fixed, .unproved),
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
  (`Acorn.Host.WritableCheckpoint.due, .fixed, .unproved),
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
  (`Acorn.Lifetime.DemonRecords.agreementRatio, .dependent, .unproved),
  (`Acorn.SwiftTd.nextReady, .dependent, .unproved),
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
  (`Acorn.Agreement.Aggregate.ratio, .fixed,
    .selection `AcornVerif.CurrentAgreement.aggregate_ratio_value),
  (`Acorn.Agreement.Channel.ratio, .dependent, .selection `Acorn.Agreement.Channel.fault_no_score),
  (`Acorn.Agreement.aggregateAll, .fixed, .selection `Acorn.Agreement.aggregateAll_missing),
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
  (`Acorn.Host.Endurance.rankIndex, .fixed, .selection `Acorn.Host.Endurance.rankIndex_bound),
  (`Acorn.Host.TileKind.harvestYield, .fixed,
    .selection `AcornVerif.CurrentCertificates.stance_yield),
  (`Acorn.Host.Viewer.GoalAchievement.State.headline, .dependent,
    .selection `Acorn.Host.Viewer.GoalAchievement.State.headline_latest),
  (`Acorn.Host.Viewer.LaunchMode.clearDisabled, .fixed,
    .selection `Acorn.Host.Viewer.fixed_clear_disabled),
  (`Acorn.Host.Viewer.browserElementBound, .fixed,
    .selection `Acorn.Host.Viewer.BrowserConstant.tileKinds_admitted),
  (`Acorn.Host.Viewer.controlWarning, .fixed, .selection `Acorn.Host.Viewer.controlWarning_active),
  (`Acorn.Portable.expSaturation, .fixed, .selection `Acorn.Portable.exp_eq_spec),
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
    .predicate `Acorn.Handcrafted.TemporalControl.finish_skill),
  (`Acorn.Host.Attempt.finished, .dependent, .predicate `Acorn.Host.Attempt.tick_finished),
  (`Acorn.Host.BoundaryDecision.closing, .dependent,
    .predicate `Acorn.Host.WritableCheckpoint.closing_due),
  (`Acorn.Host.Inventory.owns, .fixed, .predicate `Acorn.Host.Inventory.craft_exact),
  (`Acorn.Host.WritableCheckpoint.dueAt, .dependent,
    .predicate `Acorn.Host.WritableCheckpoint.closing_due)
]

/-- The entries that are judgments: each names a standing theorem. -/
theorem judged_count : (excluded.filter fun entry => entry.2.2.standing?.isSome).size = 68 := by
  decide +kernel

/-- The entries whose reason is a computed fact. -/
theorem computed_count : (excluded.filter fun entry => entry.2.2.standing?.isNone).size = 173 := by
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
  /-- The constants its body names. -/
  uses : Array Name

/-- What the walk has read so far. -/
structure Observed where
  /-- Verdict-shaped definitions of the surveyed modules. -/
  candidates : Array Candidate := #[]
  /-- Implementations of the contracts that the decision registries state. -/
  contracts : NameSet := {}
  /-- Constants that the statement of a written theorem outside the registries names. -/
  mentioned : NameSet := {}
  /-- Excluded definitions whose standing theorem was read and names them. -/
  standing : NameSet := {}
  /-- Auxiliary definitions the domain filter removed. -/
  auxiliaries : Nat := 0
  /-- Removed definitions with no source declaration before their auxiliary component. -/
  orphans : Array Name := #[]

/-- Join the observations of two environments. -/
def Observed.add (left right : Observed) : Observed :=
  { candidates := left.candidates ++ right.candidates
    contracts := right.contracts.foldl (fun all name => all.insert name) left.contracts
    mentioned := right.mentioned.foldl (fun all name => all.insert name) left.mentioned
    standing := right.standing.foldl (fun all name => all.insert name) left.standing
    auxiliaries := left.auxiliaries + right.auxiliaries
    orphans := left.orphans ++ right.orphans }

/-- The result head of a type after its arguments, with reducible definitions unfolded, and
whether a binder type or the result names one of the arguments. -/
def shapeOf (type : Expr) : MetaM (Option (Name × Shape)) :=
  forallTelescopeReducing type fun arguments body => do
    let body ← whnfR body
    let some head := body.getAppFn.constName? | return none
    let mut dependent := false
    for argument in arguments do
      if body.containsFVar argument.fvarId! then dependent := true
      let declared ← argument.fvarId!.getDecl
      for other in arguments do
        if declared.type.containsFVar other.fvarId! then dependent := true
    return some (head, if dependent then .dependent else .fixed)

/-- Whether a theorem is written in the source. Lean generates the others: an auxiliary of
another declaration, a proof field of a structure, an equation or unfolding theorem under a
reserved name, and the injectivity and size theorems of a constructor. -/
def written (env : Environment) (name : Name) : Bool :=
  let user := (privateToUserName? name).getD name
  !auxiliary user && (env.getProjectionFnInfo? name).isNone && !isReservedName env name &&
    !(match env.find? name.getPrefix with
      | some (.ctorInfo _) => true
      | _ => false)

/-- Whether a declaration exists at the name or above it. -/
def declared (env : Environment) : Name → Bool
  | .anonymous => false
  | .num parent index => env.contains (.num parent index) || declared env parent
  | .str parent component => env.contains (.str parent component) || declared env parent

/-- Read one declaration of a surveyed module. A contract of a decision registry adds its
implementation. Any other written theorem adds the constants its statement names, and
checks the entries that name it as their standing theorem. A definition that the domain
filter keeps and whose result is a verdict adds a candidate. -/
def Observed.observe (observed : Observed) (env : Environment) (owner name : Name)
    (info : ConstantInfo) : IO Observed := do
  let user := (privateToUserName? name).getD name
  match info with
  | .thmInfo _ =>
    if registries.contains owner then
      unless info.type.getAppFn.constName? == some ``Regula.ExecutableContract do
        return observed
      let some implementation := (info.type.getAppArgs[1]?).bind (·.getAppFn.constName?)
        | throw (IO.userError s!"{name}: contract names no implementation constant")
      return { observed with contracts := observed.contracts.insert implementation }
    unless written env name do return observed
    let used := info.type.getUsedConstantsAsSet
    let mut standing := observed.standing
    for (definition, _, reason) in excluded do
      if reason.standing? == some name && used.contains definition then
        standing := standing.insert definition
    return { observed with
      mentioned := used.foldl (fun all constant => all.insert constant) observed.mentioned
      standing }
  | .defnInfo definition =>
    if auxiliary user then
      let parent := sourceParent user
      let present := declared env parent ||
        (isPrivateName name && declared env (mkPrivateNameCore owner parent))
      return { observed with
        auxiliaries := observed.auxiliaries + 1
        orphans := if present then observed.orphans else observed.orphans.push name }
    let (shape, _) ← (shapeOf info.type).run'.toIO
      { fileName := "decision-inventory", fileMap := default } { env := env }
    let some (head, shape) := shape | return observed
    unless verdictHead head do return observed
    let decidable := head == ``Decidable
    let field := (env.getProjectionFnInfo? name).isSome
    let generated := match name with
      | .str parent "beq" => Lean.Meta.isInstanceCore env parent
      | _ => false
    let candidate : Candidate :=
      { name, owner, shape, structural := field || decidable, decidable := decidable && !field,
        generated, uses := definition.value.getUsedConstants }
    return { observed with candidates := observed.candidates.push candidate }
  | _ => return observed

/-- Validate the table and apply the inventory decision to every observed definition. All
failures are reported together. -/
def check (observed : Observed) : IO Unit := do
  let mut failures : Array String := #[]
  let mut candidates : NameMap Candidate := {}
  let mut applied : NameSet := observed.contracts
  for candidate in observed.candidates do
    candidates := candidates.insert candidate.name candidate
    if candidate.decidable then applied := applied.insert candidate.name
  for orphan in observed.orphans do
    failures := failures.push s!"{orphan} has an auxiliary name and no source declaration"
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
          searching := candidate.owner == searchModule
          generated := candidate.generated
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
  for candidate in observed.candidates do
    let classes : Classes :=
      ⟨candidate.structural, observed.contracts.contains candidate.name,
        valid.contains candidate.name⟩
    if classified classes then
      if classes.structural then structural := structural + 1
      if classes.contract then contracts := contracts + 1
    else if !named.contains candidate.name then
      failures := failures.push (s!"{candidate.name} has no contract and no exclusion entry " ++
        s!"(its type is {repr candidate.shape})")
    else if classes.structural && classes.contract then
      failures := failures.push s!"{candidate.name} is structural and has a contract"
  unless failures.isEmpty do
    for failure in failures do IO.eprintln s!"decision inventory: {failure}"
    throw (IO.userError s!"{failures.size} decision inventory failures")
  let count (label : String) : Nat := counts.getD label 0
  let unproved := count "unproved"
  let composed := count "composed"
  let proposal := count "proposal"
  let derived := count "derived"
  let model := count "model"
  let transition := count "transition"
  let selection := count "selection"
  let predicate := count "predicate"
  let judged := transition + selection + predicate
  IO.println (s!"decisions: {observed.candidates.size} verdict-shaped definitions: " ++
    s!"{structural} structural, {contracts} with a contract, " ++
    s!"{valid.size - judged} excluded by a computed reason (unproved {unproved}, " ++
    s!"composed {composed}, proposal {proposal}, derived {derived}, model {model}), " ++
    s!"{judged} excluded by judgment with a standing theorem " ++
    s!"(transition {transition}, selection {selection}, predicate {predicate}); " ++
    s!"{observed.auxiliaries} auxiliaries outside the domain")

end AcornDecisionInventory
