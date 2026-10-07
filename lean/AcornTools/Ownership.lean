/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Init

/-! # Maintained ownership obligations

The executable inventory is compared with Lake's evaluated configuration and
compiled module owners. The module inventory is a closed admission boundary:
new files need an explicit ownership decision, including new tools or proof
modules. This routing information does not assert semantic completeness.
Runtime sources receive source/compiled boundary admission; every project
proof receives dependent-axiom auditing. Tooling is the explicit trust boundary
listed in `AcornTools.ModuleInventory`, never an application escape hatch.
-/
namespace AcornOwnership
open Lean

/-- All reviewed maintained modules; filesystem discovery rejects missing or extra owners. -/
def modules : Array Name := #[
  `AcornTools,
  `Acorn, `Acorn.Constants, `Acorn.Admission, `Acorn.AgentDriver,
  `Acorn.Arithmetic, `Acorn.Average, `Acorn.Control,
  `Acorn.ControlDriver, `Acorn.Conversion, `Acorn.Demon,
  `Acorn.Encoding, `Acorn.Exploration, `Acorn.FeatureConstants,
  `Acorn.FeatureConsumers, `Acorn.FeatureDriver, `Acorn.FeatureHistory,
  `Acorn.FeatureLifecycle, `Acorn.FeatureModelInput, `Acorn.FeatureRanking,
  `Acorn.FeatureReferences, `Acorn.FeatureRefresh, `Acorn.FeatureRestore,
  `Acorn.Features, `Acorn.Handcrafted.Agent, `Acorn.Handcrafted.AgentAlignment,
  `Acorn.Handcrafted.AgentEpisodes, `Acorn.Handcrafted.Cumulants, `Acorn.Handcrafted.FeatureProfile,
  `Acorn.Handcrafted.GridWorld, `Acorn.Handcrafted.Observation, `Acorn.Handcrafted.PredictionControl,
  `Acorn.Handcrafted.Signals, `Acorn.Handcrafted.StepParts, `Acorn.Handcrafted.TemporalControl, `Acorn.Handcrafted.TemporalProfile, `Acorn.Host.AgentAdmission, `Acorn.Host.AgentArguments,
  `Acorn.Host.AgentAudit, `Acorn.Host.AgentDiagnostics, `Acorn.Host.AgentInterface, `Acorn.Host.AgentPrefix,
  `Acorn.Host.AuditPins, `Acorn.Host.Ansi, `Acorn.Host.Attempt, `Acorn.Host.Baseline,
  `Acorn.Host.Campaign, `Acorn.Host.Certificate, `Acorn.Host.CertificateDriver,
  `Acorn.Host.CertificateSearch, `Acorn.Host.Checkpoint.Admission, `Acorn.Host.Checkpoint.Codec,
  `Acorn.Host.Checkpoint.Frame, `Acorn.Host.Checkpoint.IO, `Acorn.Host.Checkpoint.Schema,
  `Acorn.Host.Checkpoint.Size, `Acorn.Host.Checkpoint.Snapshot, `Acorn.Host.CheckpointDiagnostic,
  `Acorn.Host.CheckpointDriver, `Acorn.Host.Cli, `Acorn.Host.Control,
  `Acorn.Host.Curriculum, `Acorn.Host.Endurance, `Acorn.Host.Geometry,
  `Acorn.Host.Metrics, `Acorn.Host.Observation, `Acorn.Host.Runner,
  `Acorn.Host.Task, `Acorn.Host.TemporalProfile, `Acorn.Host.Terrain,
  `Acorn.Host.Viewer.Admission, `Acorn.Host.Viewer.AgentTelemetry, `Acorn.Host.Viewer.Broadcast,
  `Acorn.Host.Viewer.BrowserKernel, `Acorn.Host.Viewer.BrowserMath, `Acorn.Host.Viewer.BrowserNat,
  `Acorn.Host.Viewer.BrowserRecord, `Acorn.Host.Viewer.BrowserSchema, `Acorn.Host.Viewer.BrowserStore,
  `Acorn.Host.Viewer.Buffer, `Acorn.Host.Viewer.ClockProgram, `Acorn.Host.Viewer.ControlRequest,
  `Acorn.Host.Viewer.ControlTelemetry, `Acorn.Host.Viewer.CoreTelemetry, `Acorn.Host.Viewer.FeatureTelemetry, `Acorn.Host.Viewer.GoalProtocol, `Acorn.Host.Viewer.GoalAchievement,
  `Acorn.Host.Viewer.HttpServer, `Acorn.Host.Viewer.IdentityHandshake, `Acorn.Host.Viewer.Lifecycle,
  `Acorn.Host.Viewer.LifetimeTelemetry, `Acorn.Host.Viewer.Line, `Acorn.Host.Viewer.LogPump,
  `Acorn.Host.Viewer.MapCodec, `Acorn.Host.Viewer.NativeContext, `Acorn.Host.Viewer.NativeCore,
  `Acorn.Host.Viewer.Options, `Acorn.Host.Viewer.PersistedState, `Acorn.Host.Viewer.PipePump,
  `Acorn.Host.Viewer.ProcessOwner, `Acorn.Host.Viewer.Retry, `Acorn.Host.Viewer.RunDirectory,
  `Acorn.Host.Viewer.Sensed, `Acorn.Host.Viewer.SupervisedProcess, `Acorn.Host.Viewer.Supervisor,
  `Acorn.Host.Viewer.TelemetryValue, `Acorn.Host.Viewer.Wire, `Acorn.Host.Viewer.WireNumber,
  `Acorn.Host.Viewer.WorldMemory, `Acorn.Host.Viewer.WorldTelemetry, `Acorn.Host.WorldDynamics,
  `Acorn.Host.WorldGeneration, `Acorn.Host.WorldObservation, `Acorn.Host.WorldState,
  `Acorn.Agreement, `Acorn.Interface, `Acorn.Lifetime, `Acorn.Models, `Acorn.OffPolicy, `Acorn.Options,
  `Acorn.Planning, `Acorn.Policy, `Acorn.Portable,
  `Acorn.Provenance, `Acorn.RankedFeatures, `Acorn.Rng, `Acorn.Rounding,
  `Acorn.Sarsa, `Acorn.Shuffle, `Acorn.SignalValues, `Acorn.State,
  `Acorn.SwiftTd, `Acorn.SwiftTdDriver, `Acorn.Temporal,
  `Acorn.TemporalDriver, `Acorn.Timing, `Acorn.Word, `Acorn.WorldDriver,
  `Acorn.Json,
  `AcornVerif,
  `AcornVerif.AgreementLifecycle, `AcornVerif.AgreementInterpretation, `AcornVerif.AgreementPrecision,
  `AcornVerif.AgreementReturn, `AcornVerif.AgreementTelemetryPrecision, `AcornVerif.CurrentAgreement,
  `AcornVerif.AverageReward,
  `AcornVerif.Axioms, `AcornVerif.ParameterBudget, `AcornVerif.Checkpoint,
  `AcornVerif.CurrentAccounting, `AcornVerif.CurrentOak, `AcornVerif.Oak,
  `AcornVerif.CurrentBackupBounds, `AcornVerif.CurrentConstants, `AcornVerif.CurrentRetirement, `AcornVerif.CurrentRetirementRounding,
  `AcornVerif.CurrentAgent, `AcornVerif.CurrentArithmetic, `AcornVerif.CurrentCertificates,
  `AcornVerif.CurrentCheckpoint,
  `AcornVerif.CurrentControl, `AcornVerif.CurrentCurriculum, `AcornVerif.CurrentDivision,
  `AcornVerif.CurrentExponential,
  `AcornVerif.CurrentFeatureConsumers, `AcornVerif.CurrentFloat, `AcornVerif.CurrentFloor,
  `AcornVerif.CurrentGoals, `AcornVerif.CurrentGridWorld,
  `AcornVerif.CurrentIntervals, `AcornVerif.CurrentLearner, `AcornVerif.CurrentLearnerArithmetic,
  `AcornVerif.CurrentLifetime, `AcornVerif.CurrentLifetimeArithmetic, `AcornVerif.CurrentLogarithm,
  `AcornVerif.CurrentModelArithmetic, `AcornVerif.CurrentModels, `AcornVerif.CurrentOffPolicy,
  `AcornVerif.CurrentOperations,
  `AcornVerif.CurrentOrder, `AcornVerif.CurrentPlanning, `AcornVerif.CurrentPolicyMean,
  `AcornVerif.CurrentPortable,
  `AcornVerif.CurrentPower,
  `AcornVerif.CurrentPrediction, `AcornVerif.CurrentReduction, `AcornVerif.CurrentRng,
  `AcornVerif.CurrentRunner, `AcornVerif.CurrentSeries, `AcornVerif.CurrentSpawn,
  `AcornVerif.CurrentState, `AcornVerif.CurrentStep,
  `AcornVerif.CurrentTemporal, `AcornVerif.CurrentWorld, `AcornVerif.Endurance,
  `AcornVerif.Coverage, `AcornVerif.FloatLibBridge, `AcornVerif.GridCorrespondence,
  `AcornVerif.Kernel,
  `AcornVerif.Energy, `AcornVerif.Exploration, `AcornVerif.Extragradient,
  `AcornVerif.ModelConstants, `AcornVerif.MetaGradient, `AcornVerif.Options,
  `AcornVerif.Projection,
  `AcornVerif.Retirement, `AcornVerif.Rng, `AcornVerif.StepParts, `AcornVerif.StepSize,
  `AcornVerif.TemporalSupport,
  `AcornVerif.Traces, `AcornVerif.WorldClass, `AcornVerif.WorldGoals, `Bootstrap,
  `AcornTools.Boundary.Audit, `AcornTools.Boundary.Main, `AcornTools.Corpus.Audit, `AcornTools.Corpus.Main, `AcornTools.Boundary.Departures, `AcornTools.Corpus.Browser, `AcornTools.Corpus.Documents, `AcornTools.Corpus.Pins, `AcornTools.Gate, `AcornTools.ModuleInventory,
  `NativeApp, `NativeApp.Assets, `NativeApp.BrowserKernel,
  `NativeApp.Build, `NativeApp.Core, `NativeApp.Main, `NativeApp.Report, `NativeApp.MutationAudit,
  `Acorn.Host.Viewer.NativeResources, `AcornTools.Native.Audit,
  `AcornVerif.Resource.WordKernel,
  `AcornTools.Native.Resources, `AcornTools.Native.Routes, `NativeApp.Viewer, `AcornTools.Ownership,
  `AcornTools.OwnershipAudit, `AcornTools.OwnershipSource, `AcornTools.SealedControl,
  `AcornTools.Theorems, `AcornTools.TheoremCount
]

/-- The reviewed modules of the documentation site, the separate Lake package in `site/`;
filesystem discovery rejects missing or extra owners. The site is documentation tooling over
pinned Verso, a trust boundary outside the application's proof claim. -/
def siteModules : Array Name := #[
  `AcornDocs, `AcornDocs.Verification, `AcornSite, `AcornSite.Markdown, `AcornSite.Owners,
  `AcornSite.Reference, `Main
]

/-- Native entry points, checked against both evaluated Lake targets and compiled `main`. -/
def executables : Array (String × Name) := #[
  ("swifttd-native", `Acorn.SwiftTdDriver),
  ("feature-native", `Acorn.FeatureDriver),
  ("control-native", `Acorn.ControlDriver),
  ("temporal-native", `Acorn.TemporalDriver),
  ("agent-native", `Acorn.AgentDriver),
  ("acorn-core", `NativeApp.Main),
  ("acorn-viewer", `NativeApp.Viewer),
  ("browser-kernel", `NativeApp.BrowserKernel),
  ("checkpoint-native", `Acorn.Host.CheckpointDriver),
  ("world-native", `Acorn.WorldDriver),
  ("world-certificates", `Acorn.Host.CertificateDriver),
  ("theorem-count", `AcornTools.TheoremCount),
  ("lean-boundary-audit", `AcornTools.Boundary.Main),
  ("native-audit", `AcornTools.Native.Audit),
  ("ownership-audit", `AcornTools.OwnershipAudit),
  ("corpus-audit", `AcornTools.Corpus.Main),
  ("acorn-gates", `AcornTools.Gate)
]

/-- Required composition statements must retain their actual execution references.
These are critical entry/transition obligations, not a quota or a claim that
all mathematical properties are exhausted by the inventory. -/
def anchors : Array (Name × Name × Name) := #[
  (`Acorn.Host.AgentAdmission, `Acorn.Handcrafted.AgentConstruction.admit_iff,
    `Acorn.Handcrafted.AgentConstruction.admit),
  (`Acorn.Host.AgentPrefix, `Acorn.Handcrafted.Agent.prefix_path,
    `Acorn.Handcrafted.Agent.runPrefix),
  (`Acorn.Host.AgentPrefix, `Acorn.Handcrafted.Agent.act_execution,
    `Acorn.Handcrafted.Agent.act),
  (`Acorn.Handcrafted.StepParts, `Acorn.Handcrafted.Agent.act_parts,
    `Acorn.Handcrafted.Agent.act),
  (`Acorn.Handcrafted.StepParts, `Acorn.Handcrafted.Agent.act_parts,
    `Acorn.Handcrafted.Agent.actOrdered),
  (`Acorn.Handcrafted.StepParts, `Acorn.Handcrafted.Agent.choose_keeps,
    `Acorn.Handcrafted.Agent.choose),
  (`Acorn.Handcrafted.StepParts, `Acorn.Handcrafted.Chosen.learn_rng,
    `Acorn.Handcrafted.Chosen.learn),
  (`Acorn.Handcrafted.StepParts, `Acorn.Handcrafted.Agent.actOrdered_undrawn,
    `Acorn.Handcrafted.Agent.choose),
  (`Acorn.Handcrafted.StepParts, `Acorn.Handcrafted.TemporalControl.atBoundary_unplanned,
    `Acorn.Handcrafted.TemporalControl.atBoundary),
  (`Acorn.Host.Attempt, `Acorn.Host.DecisionInput.chooseOwned_release,
    `Acorn.Host.DecisionInput.chooseOwned),
  (`Acorn.Host.Attempt, `Acorn.Host.DecisionInput.chooseOwned_release,
    `Acorn.Host.Released.learn),
  (`Acorn.Host.AgentAdmission, `Acorn.Handcrafted.AgentConstruction.callbacks_act,
    `Acorn.Handcrafted.AgentConstruction.callbacks),
  (`Acorn.Host.AgentAdmission, `Acorn.Handcrafted.DefaultConstruction.runPrefix_agent,
    `Acorn.Handcrafted.DefaultConstruction.runPrefix),
  (`Acorn.Timing, `Acorn.StepOrder.parse_spelled, `Acorn.StepOrder.parse),
  (`Acorn.Timing, `Acorn.StepOrder.tag_stored, `Acorn.StepOrder.tag),
  (`Acorn.Host.Cli, `Acorn.Host.Cli.value_absent, `Acorn.Host.Cli.value),
  (`Acorn.Host.Cli, `Acorn.Host.Cli.value_follows, `Acorn.Host.Cli.value),
  (`Acorn.Host.Cli, `Acorn.Host.Cli.value_missing, `Acorn.Host.Cli.value),
  (`Acorn.Host.Cli, `Acorn.Host.Cli.stepOrderValue_iff, `Acorn.Host.Cli.stepOrderValue),
  (`Acorn.Host.Cli, `Acorn.Host.Cli.stepOrder_iff, `Acorn.Host.Cli.stepOrder),
  (`Acorn.Host.Cli, `Acorn.Host.Cli.stepOrder_refused, `Acorn.Host.Cli.stepOrder),
  (`Acorn.Host.Checkpoint.Admission, `Acorn.Checkpoint.admitHeader_iff,
    `Acorn.Checkpoint.admitHeader),
  (`Acorn.Host.Checkpoint.Admission, `Acorn.Checkpoint.loadCandidate_header,
    `Acorn.Checkpoint.loadCandidate),
  (`Acorn.Host.Checkpoint.Admission, `Acorn.Checkpoint.load_candidate, `Acorn.Checkpoint.load),
  (`AcornVerif.CurrentCheckpoint, `AcornVerif.CurrentCheckpoint.saved_header,
    `Acorn.Checkpoint.saveBytes),
  (`AcornVerif.CurrentCheckpoint, `AcornVerif.CurrentCheckpoint.saved_admitted_order,
    `Acorn.Checkpoint.saveBytes),
  (`AcornVerif.CurrentCheckpoint, `AcornVerif.CurrentCheckpoint.saved_admitted_order,
    `Acorn.Checkpoint.loadCandidate),
  (`AcornVerif.CurrentCheckpoint, `AcornVerif.CurrentCheckpoint.image_roundtrip,
    `Acorn.Checkpoint.admitPayload),
  (`AcornVerif.CurrentCheckpoint, `AcornVerif.CurrentCheckpoint.image_roundtrip,
    `Acorn.Checkpoint.imagePayload),
  (`Acorn.Host.Attempt, `Acorn.Host.Attempt.complete_learned, `Acorn.Host.Attempt.complete),
  (`Acorn.Host.Runner, `Acorn.Host.runAttemptSteps_complete, `Acorn.Host.runAttemptSteps),
  (`Acorn.Host.Runner, `Acorn.Host.runReleasedSteps_complete, `Acorn.Host.runReleasedSteps),
  (`Acorn.Host.Runner, `Acorn.Host.campaignStep_attempt, `Acorn.Host.campaignStep),
  (`Acorn.Host.AgentInterface, `Acorn.Handcrafted.Agent.callbacks_act,
    `Acorn.Handcrafted.Agent.callbacks),
  (`Acorn.Host.AgentInterface, `Acorn.Handcrafted.Agent.observe_predictions,
    `Acorn.Handcrafted.Agent.observe),
  (`Acorn.Host.AgentInterface, `Acorn.Handcrafted.Agent.grid_inputs,
    `Acorn.Handcrafted.Grid.frame),
  (`AcornVerif.GridCorrespondence, `AcornVerif.GridCorrespondence.initial_eq,
    `Acorn.Handcrafted.Agent.initial),
  (`AcornVerif.GridCorrespondence, `AcornVerif.GridCorrespondence.act_eq,
    `Acorn.Handcrafted.Agent.act),
  (`AcornVerif.GridCorrespondence, `AcornVerif.GridCorrespondence.callback_eq,
    `Acorn.Handcrafted.Agent.callbacks),
  (`AcornVerif.GridCorrespondence, `AcornVerif.GridCorrespondence.restore_eq,
    `Acorn.Handcrafted.Agent.restore),
  (`Acorn.Host.Checkpoint.Frame, `Acorn.Checkpoint.roundtrip, `Acorn.Checkpoint.encode),
  (`Acorn.Host.Checkpoint.Frame, `Acorn.Checkpoint.roundtrip, `Acorn.Checkpoint.decode),
  (`Acorn.Host.Checkpoint.Admission, `Acorn.Checkpoint.load_nonmutation, `Acorn.Checkpoint.load),
  (`Acorn.Host.Viewer.Admission, `Acorn.Host.Viewer.Admission.rejected_preserves_history,
    `Acorn.Host.Viewer.Admission.receive),
  (`Acorn.Host.Viewer.Admission, `Acorn.Host.Viewer.Admission.stored_capture,
    `Acorn.Host.Viewer.Admission.receive),
  (`Acorn.Host.Viewer.Lifecycle, `Acorn.Host.Viewer.Lifecycle.stale_preserves,
    `Acorn.Host.Viewer.Lifecycle.admit),
  (`Acorn.Host.Viewer.Lifecycle, `Acorn.Host.Viewer.Lifecycle.retire_revokes,
    `Acorn.Host.Viewer.Lifecycle.retire),
  (`Acorn.Host.Viewer.BrowserSchema, `Acorn.Host.Viewer.browserSchema_execution,
    `Acorn.Host.Viewer.coreTelemetry),
  (`Acorn.Host.Viewer.BrowserRecord, `Acorn.Host.Viewer.browserRecord_keys,
    `Acorn.Host.Viewer.browserRecordFields),
  (`Acorn.Host.Viewer.BrowserStore, `Acorn.Host.Viewer.browserColumns_live,
    `Acorn.Host.Viewer.browserColumns),
  (`NativeApp.MutationAudit, `NativeApp.AuditArm.incumbent_profile,
    `NativeApp.AuditArm.construction),
  (`AcornVerif.CurrentCertificates, `AcornVerif.CurrentCertificates.replay_feasible,
    `Acorn.Host.replayCertified),
  (`AcornVerif.CurrentCertificates, `AcornVerif.CurrentCertificates.blocked_outside,
    `Acorn.Host.regionBlocked),
  (`AcornVerif.CurrentCertificates, `AcornVerif.CurrentCertificates.stance_harvest,
    `Acorn.Host.stanceCertified)
]

/-- Types whose values carry a claim about their makers that the type does not prove:
the state, the image and the chosen value of one construction are of that construction's
step order, and a callback record is of the order in its index. The constructor of each
must be sealed: private, or a row of `sealedConstants`. A change of visibility that
removes one from the rule fails the audit. -/
def sealedTypes : Array Name := #[
  `Acorn.Handcrafted.AgentConstruction.State, `Acorn.Handcrafted.AgentConstruction.Image,
  `Acorn.Handcrafted.AgentConstruction.Chosen, `Acorn.Handcrafted.Chosen,
  `Acorn.Host.AgentCallbacks]

/-- Constants with a public name that only the listed modules may reference in a
definition. The audit computes the other sealed constants and has no row for them: every
private constructor of a project type with its declaring module, every alias of a sealed
constructor (found by its body), and every definition of an owning module that references
a sealed constant and is not an entry of `interface`.

- The constructor of the callback record: its declaring module, the agent's two parts
  (`Agent.callbacks`) and the construction's callbacks (`AgentConstruction.callbacks`).
- The constructor of the image of a construction: its declaring module and its two
  makers, the admission of a payload and the snapshot of a state.
- The callbacks of a construction: the module that defines them and derives them for a
  campaign (`AgentConstruction.runCampaign`), and the ANSI entry, which makes its own
  construction of the default order. No other module gets the two parts of a
  construction, as a record or as functions. -/
def sealedConstants : Array (Name × Array Name) := #[
  (`Acorn.Host.AgentCallbacks.mk,
    #[`Acorn.Host.Attempt, `Acorn.Host.AgentInterface, `Acorn.Host.AgentAdmission]),
  (`Acorn.Handcrafted.AgentConstruction.Image.mk,
    #[`Acorn.Host.AgentAdmission, `Acorn.Host.Checkpoint.Admission,
      `Acorn.Host.Checkpoint.Snapshot]),
  (`Acorn.Handcrafted.AgentConstruction.callbacks,
    #[`Acorn.Host.AgentAdmission, `NativeApp.Core])
]

/-- The interface of the owning modules: the definitions that reference a sealed constant
and that every module may use. Every other such definition is sealed. The audit infers no
entry and reads no type; this list is the reviewed decision, and a change of it is a
change of the invariant.

No statement "this value has the order of its construction" exists for a state or an
image, because neither holds an order: the order is a fact about the code that made the
value. Each entry thus has one of two things. It names a theorem whose statement names
the entry and says where its value comes from, with one line on what that theorem states.
Or it has no theorem, and its line says why no statement exists and what the entry gives
to its caller.

The audit requires that each entry references a sealed constant, that a named theorem
exists and names the entry, and that each entry has its line. -/
def interface : Array (Name × Option Name × String) := #[
  (`Acorn.Handcrafted.AgentConstruction.initial,
    some `Acorn.Handcrafted.AgentConstruction.initial_agent,
    "Maker. The state is the agent's cold initial state: no step is in its history."),
  (`Acorn.Handcrafted.AgentConstruction.runCampaign,
    some `Acorn.Handcrafted.AgentConstruction.runCampaign_callbacks,
    "Maker. The campaign is the host campaign over the construction's cold initial state and its own callbacks, whose whole step is the agent's step of the construction's order (`AgentConstruction.callbacks_act`)."),
  (`Acorn.Handcrafted.Agent.choose, some `Acorn.Handcrafted.Agent.choose_selected,
    "Maker. The chosen value holds the order that the first part selected under: this is a statement of the order, because this value stores one."),
  (`Acorn.Handcrafted.AgentConstruction.State.restore,
    some `Acorn.Handcrafted.AgentConstruction.State.restore_agent,
    "Carrier. It takes a state and an image of one construction, and the result is the agent's own restore of that image on that state."),
  (`Acorn.Handcrafted.AgentConstruction.State.censorObservations,
    some `Acorn.Handcrafted.AgentConstruction.State.censorObservations_agent,
    "Carrier. It takes a state of a construction, and the result is the agent's own censoring of that state: no step is taken."),
  (`Acorn.Handcrafted.DefaultConstruction.runPrefix,
    some `Acorn.Handcrafted.DefaultConstruction.runPrefix_agent,
    "Carrier. It takes a state of a construction that holds the proof of the default order, and the result is the agent's own prefix fold, whose step is the step of that order."),
  (`Acorn.Checkpoint.load, some `Acorn.Checkpoint.load_candidate,
    "Carrier. It takes a state of a construction, and the result is that state restored from a candidate that the same construction admitted from the bytes (`Checkpoint.loadCandidate_header`)."),
  (`Acorn.Checkpoint.saveBytes, some `AcornVerif.CurrentCheckpoint.saved_header,
    "Consumer. It takes a state of a construction and returns bytes, whose header holds the stored word of that construction's order."),
  (`Acorn.Handcrafted.Chosen._sizeOf_inst, none,
    "Generated. No statement exists for it. It is the size measure that Lean generates for the chosen value: a function from the value to a number, which gives no value. The generated measure of the construction's chosen value, in another module, references it."),
  (`Acorn.Handcrafted.AgentConstruction.execute, some `AcornVerif.CurrentAgent.native_prefix,
    "Maker. The finite prefix from cold initialization, for a construction that holds the proof of the default order: the theorem states that the result is the agent's own prefix path from the cold initial state."),
  (`NativeApp.runCore, none,
    "Plain result. No statement exists for it. It is the command dispatch of the core: it runs a campaign, an audit or the ANSI view of a construction that it makes itself, and it returns an exit code. No value of a sealed type leaves it. The entry module references it.")
]

/-- Required native entry dependencies after proof erasure. These are routing
obligations; the IR graph alone does not prove control-flow or argument semantics.
Erased ANSI and checksum parameters select the compiler's reduced-arity owners. -/
def entryUses : Array (Name × Array Name) := #[
  (`NativeApp.Main, #[`NativeApp.streamingOptions, `Acorn.Host.Viewer.runNativeCampaign,
    `Acorn.Host.StopFlag.withCommands._redArg,
    `Acorn.Handcrafted.Agent.callbacks, `Acorn.Handcrafted.AgentConstruction.callbacks,
    `Acorn.Handcrafted.AgentConstruction.runCampaign,
    `Acorn.Checkpoint.Store.hooks,
    `Acorn.Host.runAnsi._redArg, `Acorn.Host.agentChecksum._redArg, `NativeApp.runMutationAudit,
    `NativeApp.AuditArm.construction]),
  (`NativeApp.Viewer, #[`NativeApp.runViewer, `Acorn.Host.Viewer.ViewerOptions.decode,
    `Acorn.Host.Viewer.Supervisor.new, `Acorn.Host.Viewer.Supervisor.step]),
  (`NativeApp.BrowserKernel, #[`Acorn.Host.Viewer.browserKernelJavascript]),
  (`Acorn.SwiftTdDriver, #[`Acorn.SwiftTdDriver.execute]),
  (`Acorn.FeatureDriver, #[`Acorn.FeatureDriver.execute]),
  (`Acorn.ControlDriver, #[`Acorn.ControlDriver.execute]),
  (`Acorn.TemporalDriver, #[`Acorn.TemporalDriver.execute]),
  (`Acorn.AgentDriver, #[`Acorn.AgentDriver.execute]),
  (`Acorn.WorldDriver, #[`Acorn.WorldDriver.execute]),
  (`Acorn.Host.CheckpointDriver, #[`Acorn.Host.CheckpointDriver.dispatch]),
  (`Acorn.Host.CertificateDriver, #[`Acorn.Host.CertificateDriver.execute,
    `Acorn.Host.replayCertified, `Acorn.Host.regionBlocked, `Acorn.Host.stanceCertified]),
  (`AcornTools.Boundary.Main, #[`AcornBoundaryAudit.command]),
  (`AcornTools.TheoremCount, #[`AcornTheoremCount.inventory]),
  (`AcornTools.Native.Audit, #[`AcornNativeAudit.audit]),
  (`AcornTools.OwnershipAudit, #[`AcornOwnershipAudit.compiled]),
  (`AcornTools.Corpus.Main, #[`AcornCorpus.check]),
  (`AcornTools.Gate, #[`AcornGate.verify])
]

end AcornOwnership
