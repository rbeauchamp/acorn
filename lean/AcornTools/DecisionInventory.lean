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
fails verification, and so does an entry of `excluded` that names no verdict-shaped
definition or states another shape than the definition has. A new verdict-shaped definition
therefore cannot arrive unlisted, and a contract cannot be removed without an entry here.

This is a check that every such definition has been classified. Whether each reason is the
right one is review: `Reason` states what each claims.
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

/-- Why a verdict-shaped definition carries no contract. The first three are not decisions:
their result does not accept or refuse an input. The next three are decisions with no theorem
of their own about the inputs they accept. The last two are not written or run as decisions
of an executable. -/
inductive Reason where
  /-- The result is the outcome of a state transition or of a computation step. A refusal
  reports that the step did not happen; the theorems about the transition stand. -/
  | transition
  /-- The optional result is a selection, a lookup or a derived value. An absent result
  reports that there is nothing to return, not that an input is refused. -/
  | selection
  /-- A Boolean property of state the library has already admitted. It selects a branch of a
  transition and refuses no input. -/
  | predicate
  /-- An admission that applies other admissions in sequence, with no theorem of its own
  about the inputs it accepts. The contracts of the admissions it applies stand. -/
  | composed
  /-- A function that proposes a certificate. A registered checker decides every proposal. -/
  | proposal
  /-- A parser, a decoder or a validity test with no theorem about the inputs it accepts, so
  no direction of its verdict is proved. What stands is the type of an accepted value. -/
  | unproved
  /-- A comparison that Lean generates for a `deriving` clause. -/
  | derived
  /-- A definition of the proof library, which has no executable. Its theorems relate it to
  the executing definitions, and no claim rests on running it. -/
  | model
  deriving DecidableEq, Repr

/-- The decision registries: the modules whose contracts count toward the inventory. -/
def registries : Array Name := #[`Acorn.Decisions, `AcornVerif.Decisions]

/-- The classes of one verdict-shaped definition, as the ownership audit reads them. -/
structure Classes where
  /-- A structure field or a function with a `Decidable` result. -/
  structural : Bool
  /-- The implementation of a contract of a decision registry. -/
  contract : Bool
  /-- Named by exactly one entry of `excluded`, which states the shape its type has. -/
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

/-- Every verdict-shaped definition of the claimed libraries that is neither structural nor
the implementation of a contract, with the shape of its type and its reason. -/
def excluded : Array (Name × Shape × Reason) := #[
  (`Acorn.Agreement.Total.observe, .dependent, .transition),
  (`Acorn.Features.ExploratoryRun.serve, .dependent, .transition),
  (`Acorn.Handcrafted.Agent.input, .dependent, .transition),
  (`Acorn.Handcrafted.Agent.runPrefix, .dependent, .transition),
  (`Acorn.Handcrafted.AgentConstruction.execute, .dependent, .transition),
  (`Acorn.Handcrafted.TemporalControl.atBoundary, .dependent, .transition),
  (`Acorn.Handcrafted.TemporalControl.dispatchMeta, .dependent, .transition),
  (`Acorn.Handcrafted.TemporalControl.select, .dependent, .transition),
  (`Acorn.Handcrafted.TemporalControl.selectWithOperations, .dependent, .transition),
  (`Acorn.Handcrafted.TemporalControl.serve, .dependent, .transition),
  (`Acorn.Handcrafted.TemporalControl.step, .dependent, .transition),
  (`Acorn.Host.AnsiState.refresh, .dependent, .transition),
  (`Acorn.Host.AnsiState.tick, .dependent, .transition),
  (`Acorn.Host.Attempt.finish, .dependent, .transition),
  (`Acorn.Host.Attempt.prepare, .dependent, .transition),
  (`Acorn.Host.Attempt.sense, .dependent, .transition),
  (`Acorn.Host.Attempt.tick, .dependent, .transition),
  (`Acorn.Host.BaselineAttempt.run, .dependent, .transition),
  (`Acorn.Host.BaselineAttempt.tick, .dependent, .transition),
  (`Acorn.Host.OwnedStep.environment, .dependent, .transition),
  (`Acorn.Host.PreparedStep.commit, .dependent, .transition),
  (`Acorn.Host.PreparedStep.environment, .dependent, .transition),
  (`Acorn.Host.Viewer.Lifecycle.archived, .fixed, .transition),
  (`Acorn.Host.Viewer.Lifecycle.beginArchive, .fixed, .transition),
  (`Acorn.Host.Viewer.Lifecycle.reserve, .fixed, .transition),
  (`Acorn.Host.Viewer.PersistedState.launch, .fixed, .transition),
  (`Acorn.Host.World.advanceActions, .dependent, .transition),
  (`Acorn.Host.World.enterable, .dependent, .transition),
  (`Acorn.Host.World.initial, .dependent, .transition),
  (`Acorn.Host.World.observe, .dependent, .transition),
  (`Acorn.Host.World.observeTile, .dependent, .transition),
  (`Acorn.Host.World.step, .dependent, .transition),
  (`Acorn.Host.World.tileKind, .dependent, .transition),
  (`Acorn.Host.considerSpawn, .dependent, .transition),
  (`Acorn.Host.countKindNear, .dependent, .transition),
  (`Acorn.Host.fbm, .fixed, .transition),
  (`Acorn.Host.foodTrials, .dependent, .transition),
  (`Acorn.Host.initializeDeer, .dependent, .transition),
  (`Acorn.Host.octaveLoop, .fixed, .transition),
  (`Acorn.Host.passiveChange, .dependent, .transition),
  (`Acorn.Host.payAndAct, .dependent, .transition),
  (`Acorn.Host.performAction, .dependent, .transition),
  (`Acorn.Host.placeDeer, .dependent, .transition),
  (`Acorn.Host.runBaselineCampaign, .dependent, .transition),
  (`Acorn.Host.runRandomBaseline, .fixed, .transition),
  (`Acorn.Host.selectSpawn, .dependent, .transition),
  (`Acorn.Host.spawnFood, .dependent, .transition),
  (`Acorn.Host.terrain, .fixed, .transition),
  (`Acorn.Host.valueNoise, .fixed, .transition),
  (`Acorn.Host.wanderDeer, .dependent, .transition),
  (`Acorn.Host.wanderPopulation, .dependent, .transition),
  (`Acorn.WorldDriver.execute, .fixed, .transition),
  (`Acorn.WorldDriver.executeTerrain, .fixed, .transition),
  (`Acorn.Agreement.Aggregate.ratio, .fixed, .selection),
  (`Acorn.Agreement.Channel.ratio, .dependent, .selection),
  (`Acorn.Agreement.Total.ratio, .dependent, .selection),
  (`Acorn.Agreement.aggregateAll, .fixed, .selection),
  (`Acorn.Features.Assignment.feature, .dependent, .selection),
  (`Acorn.Features.Assignment.identity, .dependent, .selection),
  (`Acorn.Features.Assignment.retain, .dependent, .selection),
  (`Acorn.Features.Lifecycle.candidate, .dependent, .selection),
  (`Acorn.Features.Lifecycle.prefer, .dependent, .selection),
  (`Acorn.Features.Occupancy.executing, .dependent, .selection),
  (`Acorn.Features.RankedFeatures.position, .dependent, .selection),
  (`Acorn.Features.TemporalDecision.episodeEnd, .dependent, .selection),
  (`Acorn.Features.best, .dependent, .selection),
  (`Acorn.Features.candidateOfWeight, .dependent, .selection),
  (`Acorn.Features.kept, .dependent, .selection),
  (`Acorn.Handcrafted.TemporalControl.activeSlot, .dependent, .selection),
  (`Acorn.Handcrafted.TemporalControl.takeoverValue, .dependent, .selection),
  (`Acorn.Handcrafted.skillOfMeta, .fixed, .selection),
  (`Acorn.Host.Action.direction, .fixed, .selection),
  (`Acorn.Host.Endurance.energyQuantile, .fixed, .selection),
  (`Acorn.Host.Endurance.mean, .fixed, .selection),
  (`Acorn.Host.Endurance.rankIndex, .fixed, .selection),
  (`Acorn.Host.TileKind.harvestYield, .fixed, .selection),
  (`Acorn.Host.Viewer.BrowserColumn.view, .fixed, .selection),
  (`Acorn.Host.Viewer.BrowserConversion.finite, .fixed, .selection),
  (`Acorn.Host.Viewer.BrowserConversion.numbers, .fixed, .selection),
  (`Acorn.Host.Viewer.Buffer.pop, .dependent, .selection),
  (`Acorn.Host.Viewer.GoalAchievement.State.headline, .dependent, .selection),
  (`Acorn.Host.Viewer.LaunchMode.clearDisabled, .fixed, .selection),
  (`Acorn.Host.Viewer.Lifecycle.archiveIntent, .fixed, .selection),
  (`Acorn.Host.Viewer.LineDecoder.finish, .fixed, .selection),
  (`Acorn.Host.Viewer.browserElementBound, .fixed, .selection),
  (`Acorn.Host.Viewer.browserIndexBound, .fixed, .selection),
  (`Acorn.Host.Viewer.controlWarning, .fixed, .selection),
  (`Acorn.Lifetime.DemonRecords.agreementRatio, .dependent, .selection),
  (`Acorn.Portable.expSaturation, .fixed, .selection),
  (`NativeApp.buildIdentity, .fixed, .selection),
  (`Acorn.Binary32.negative, .fixed, .predicate),
  (`Acorn.Features.Assignment.potential, .dependent, .predicate),
  (`Acorn.Features.Ensemble.holds, .dependent, .predicate),
  (`Acorn.Features.Interface.reserved, .fixed, .predicate),
  (`Acorn.Features.Lifecycle.eligible, .dependent, .predicate),
  (`Acorn.Features.Lifecycle.mature, .dependent, .predicate),
  (`Acorn.Features.Occupancy.free, .dependent, .predicate),
  (`Acorn.Features.OptionActivation.learning, .dependent, .predicate),
  (`Acorn.Features.TemporalDecision.own, .dependent, .predicate),
  (`Acorn.Handcrafted.FeatureProfile.ranksSubtasks, .fixed, .predicate),
  (`Acorn.Handcrafted.FeatureProfile.usesHierarchy, .fixed, .predicate),
  (`Acorn.Handcrafted.askedBy, .dependent, .predicate),
  (`Acorn.Handcrafted.spatialPotential, .fixed, .predicate),
  (`Acorn.Host.Attempt.finished, .dependent, .predicate),
  (`Acorn.Host.BoundaryDecision.closing, .dependent, .predicate),
  (`Acorn.Host.Inventory.owns, .fixed, .predicate),
  (`Acorn.Host.Viewer.Lifecycle.checkpointRefusedValue, .fixed, .predicate),
  (`Acorn.Host.Viewer.WorldMemory.isIncomplete, .dependent, .predicate),
  (`Acorn.Host.WritableCheckpoint.due, .fixed, .predicate),
  (`Acorn.Host.WritableCheckpoint.dueAt, .dependent, .predicate),
  (`Acorn.Host.foodDue, .fixed, .predicate),
  (`Acorn.SwiftTd.nextReady, .dependent, .predicate),
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
  (`Acorn.AgentDriver.dispatch, .fixed, .unproved),
  (`Acorn.Checkpoint.temporaryPath, .fixed, .unproved),
  (`Acorn.Host.AgentArguments.admit, .fixed, .unproved),
  (`Acorn.Host.AgentArguments.profile, .fixed, .unproved),
  (`Acorn.Host.AgentArguments.word, .fixed, .unproved),
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
  (`Acorn.Host.Cli.value, .fixed, .unproved),
  (`Acorn.Host.Viewer.BrowserColumn.fits, .fixed, .unproved),
  (`Acorn.Host.Viewer.BrowserConversion.fits, .fixed, .unproved),
  (`Acorn.Host.Viewer.BrowserConversion.indexed, .fixed, .unproved),
  (`Acorn.Host.Viewer.BrowserConversion.number, .fixed, .unproved),
  (`Acorn.Host.Viewer.BrowserMath.Test.eval, .fixed, .unproved),
  (`Acorn.Host.Viewer.BrowserProperty.fits, .fixed, .unproved),
  (`Acorn.Host.Viewer.Capture.after, .fixed, .unproved),
  (`Acorn.Host.Viewer.Capture.follows, .fixed, .unproved),
  (`Acorn.Host.Viewer.ClockProgram.Predicate.eval, .dependent, .unproved),
  (`Acorn.Host.Viewer.Command.parse, .fixed, .unproved),
  (`Acorn.Host.Viewer.Envelope.parse, .fixed, .unproved),
  (`Acorn.Host.Viewer.HealthEnvelope.parse, .fixed, .unproved),
  (`Acorn.Host.Viewer.Identity.browserSafe, .fixed, .unproved),
  (`Acorn.Host.Viewer.Lifecycle.acceptsFailure, .fixed, .unproved),
  (`Acorn.Host.Viewer.Lifecycle.ownsIdentity, .fixed, .unproved),
  (`Acorn.Host.Viewer.LineBytes.text, .fixed, .unproved),
  (`Acorn.Host.Viewer.MapBytes.admit, .dependent, .unproved),
  (`Acorn.Host.Viewer.PersistedState.decode, .fixed, .unproved),
  (`Acorn.Host.Viewer.Retry.exhausted, .fixed, .unproved),
  (`Acorn.Host.Viewer.Retry.ready, .fixed, .unproved),
  (`Acorn.Host.Viewer.SensedEnvelope.parse, .fixed, .unproved),
  (`Acorn.Host.Viewer.ViewerOptions.decode, .fixed, .unproved),
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
  (`Acorn.Host.controlWhitespace, .fixed, .unproved),
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
  (`Acorn.WorldDriver.coordinate, .fixed, .unproved),
  (`Acorn.WorldDriver.dispatch, .fixed, .unproved),
  (`Acorn.WorldDriver.word, .fixed, .unproved),
  (`NativeApp.AuditArm.options, .fixed, .unproved),
  (`NativeApp.auditHex, .fixed, .unproved),
  (`NativeApp.auditOptions, .fixed, .unproved),
  (`NativeApp.decodeBuildIdentity, .fixed, .unproved),
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
  (`AcornVerif.TemporalSupport.outcomes, .dependent, .model)
]

/-- The result heads that make a definition verdict-shaped. -/
def verdictHead (name : Name) : Bool :=
  name == ``Bool || name == ``Option || name == ``Except || name == ``Decidable

/-- What the walk of the compiled environment reads about one verdict-shaped definition. -/
structure Candidate where
  /-- The definition. -/
  name : Name
  /-- The shape of its type. -/
  shape : Shape
  /-- A structure field or a function with a `Decidable` result. -/
  structural : Bool

/-- The verdict-shaped definitions and the contract implementations seen so far. -/
structure Observed where
  /-- Verdict-shaped definitions of the surveyed modules. -/
  candidates : Array Candidate := #[]
  /-- Implementations of the contracts that the decision registries state. -/
  contracts : NameSet := {}

/-- Join the observations of two environments. -/
def Observed.add (left right : Observed) : Observed :=
  { candidates := left.candidates ++ right.candidates
    contracts := right.contracts.foldl (fun all name => all.insert name) left.contracts }

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

/-- Read one declaration of a surveyed module: a contract of a decision registry adds its
implementation, and a verdict-shaped definition adds a candidate. Compiler-generated
auxiliary definitions are not definitions of the source. -/
def Observed.observe (observed : Observed) (env : Environment) (owner name : Name)
    (info : ConstantInfo) : IO Observed := do
  match info with
  | .thmInfo _ =>
    if registries.contains owner &&
        info.type.getAppFn.constName? == some ``Regula.ExecutableContract then
      let some implementation := (info.type.getAppArgs[1]?).bind (·.getAppFn.constName?)
        | throw (IO.userError s!"{name}: contract names no implementation constant")
      return { observed with contracts := observed.contracts.insert implementation }
    return observed
  | .defnInfo _ =>
    if name.isInternalDetail || name.isImplementationDetail ||
        (name.toString.splitOn "._").length > 1 then return observed
    let (shape, _) ← (shapeOf info.type).run'.toIO
      { fileName := "decision-inventory", fileMap := default } { env := env }
    let some (head, shape) := shape | return observed
    unless verdictHead head do return observed
    let structural := (env.getProjectionFnInfo? name).isSome || head == ``Decidable
    return { observed with candidates := observed.candidates.push ⟨name, shape, structural⟩ }
  | _ => return observed

/-- Apply the inventory decision to every observed definition and refuse a stale entry. All
failures are reported together. -/
def check (observed : Observed) : IO Unit := do
  let mut failures := 0
  let mut structural := 0
  let mut contracts := 0
  let mut seen : NameSet := {}
  for candidate in observed.candidates do
    seen := seen.insert candidate.name
    let entries := excluded.filter (·.1 == candidate.name)
    let listed := entries.size == 1 && entries.all (·.2.1 == candidate.shape)
    let classes : Classes :=
      ⟨candidate.structural, observed.contracts.contains candidate.name, listed⟩
    if classified classes then
      if classes.structural then structural := structural + 1
      if classes.contract then contracts := contracts + 1
    else
      failures := failures + 1
      let detail :=
        if entries.size > 1 then "has more than one exclusion entry"
        else if entries.any (·.2.1 != candidate.shape) then
          s!"is excluded with another shape than its type has ({repr candidate.shape})"
        else if classes.contract && !entries.isEmpty then "has a contract and an exclusion entry"
        else if classes.structural && (classes.contract || !entries.isEmpty) then
          "is structural and also has a contract or an exclusion entry"
        else s!"has no contract and no exclusion entry (its type is {repr candidate.shape})"
      IO.eprintln s!"decision inventory: {candidate.name} {detail}"
  for (name, _, _) in excluded do
    unless seen.contains name do
      failures := failures + 1
      IO.eprintln
        s!"decision inventory: exclusion entry {name} names no verdict-shaped definition"
  unless failures == 0 do throw (IO.userError s!"{failures} decision inventory failures")
  IO.println (s!"decisions: {observed.candidates.size} verdict-shaped definitions: " ++
    s!"{structural} structural, {contracts} with a contract, " ++
    s!"{excluded.size} excluded with a reason")

end AcornDecisionInventory
