/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean

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
  `Acorn.Handcrafted.Observation, `Acorn.Handcrafted.PredictionControl, `Acorn.Handcrafted.TemporalControl,
  `Acorn.Handcrafted.TemporalProfile, `Acorn.Host.AgentAdmission, `Acorn.Host.AgentArguments,
  `Acorn.Host.AgentAudit, `Acorn.Host.AgentDiagnostics, `Acorn.Host.AgentInterface, `Acorn.Host.AgentPrefix,
  `Acorn.Host.AuditPins, `Acorn.Host.Ansi, `Acorn.Host.Attempt, `Acorn.Host.Baseline,
  `Acorn.Host.Campaign, `Acorn.Host.Checkpoint.Admission, `Acorn.Host.Checkpoint.Codec,
  `Acorn.Host.Checkpoint.Frame, `Acorn.Host.Checkpoint.IO, `Acorn.Host.Checkpoint.Schema,
  `Acorn.Host.Checkpoint.Size, `Acorn.Host.Checkpoint.Snapshot, `Acorn.Host.CheckpointDiagnostic,
  `Acorn.Host.CheckpointDriver, `Acorn.Host.Cli, `Acorn.Host.Control,
  `Acorn.Host.Curriculum, `Acorn.Host.Endurance, `Acorn.Host.Geometry,
  `Acorn.Host.Metrics, `Acorn.Host.Observation, `Acorn.Host.Runner,
  `Acorn.Host.Task, `Acorn.Host.TemporalProfile, `Acorn.Host.Terrain,
  `Acorn.Host.Viewer.Admission, `Acorn.Host.Viewer.AgentTelemetry, `Acorn.Host.Viewer.Broadcast,
  `Acorn.Host.Viewer.BrowserMath, `Acorn.Host.Viewer.BrowserNat, `Acorn.Host.Viewer.BrowserSchema,
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
  `Acorn.Agreement, `Acorn.Lifetime, `Acorn.Models, `Acorn.Options,
  `Acorn.Planning, `Acorn.Policy, `Acorn.Portable,
  `Acorn.Provenance, `Acorn.Rng, `Acorn.Rounding,
  `Acorn.Sarsa, `Acorn.Shuffle, `Acorn.State,
  `Acorn.SwiftTd, `Acorn.SwiftTdDriver, `Acorn.Temporal,
  `Acorn.TemporalDriver, `Acorn.Word, `Acorn.WorldDriver,
  `Acorn.Json,
  `AcornVerif,
  `AcornVerif.AgreementLifecycle, `AcornVerif.AgreementInterpretation, `AcornVerif.AgreementPrecision,
  `AcornVerif.AgreementReturn, `AcornVerif.AgreementTelemetryPrecision, `AcornVerif.CurrentAgreement,
  `AcornVerif.AverageReward,
  `AcornVerif.Axioms, `AcornVerif.BigWorld, `AcornVerif.Checkpoint,
  `AcornVerif.CurrentBackupBounds, `AcornVerif.CurrentConstants, `AcornVerif.CurrentRetirement, `AcornVerif.CurrentRetirementRounding,
  `AcornVerif.CurrentAgent, `AcornVerif.CurrentArithmetic, `AcornVerif.CurrentCheckpoint,
  `AcornVerif.CurrentControl, `AcornVerif.CurrentDivision, `AcornVerif.CurrentExponential,
  `AcornVerif.CurrentFeatureConsumers, `AcornVerif.CurrentFloat, `AcornVerif.CurrentFloor,
  `AcornVerif.CurrentIntervals, `AcornVerif.CurrentLearner, `AcornVerif.CurrentLearnerArithmetic,
  `AcornVerif.CurrentLifetime, `AcornVerif.CurrentLifetimeArithmetic, `AcornVerif.CurrentLogarithm,
  `AcornVerif.CurrentModelArithmetic, `AcornVerif.CurrentModels, `AcornVerif.CurrentOperations,
  `AcornVerif.CurrentOrder, `AcornVerif.CurrentPortable, `AcornVerif.CurrentPower,
  `AcornVerif.CurrentPrediction, `AcornVerif.CurrentReduction, `AcornVerif.CurrentRng,
  `AcornVerif.CurrentRunner, `AcornVerif.CurrentSeries, `AcornVerif.CurrentState,
  `AcornVerif.CurrentTemporal, `AcornVerif.CurrentWorld, `AcornVerif.Endurance,
  `AcornVerif.Energy, `AcornVerif.Exploration,
  `AcornVerif.ModelConstants, `AcornVerif.MetaGradient, `AcornVerif.Options,
  `AcornVerif.Projection,
  `AcornVerif.Retirement, `AcornVerif.Rng, `AcornVerif.StepSize,
  `AcornVerif.TemporalSupport,
  `AcornVerif.Traces, `AcornVerif.WorldGoals, `Bootstrap,
  `AcornTools.Boundary.Audit, `AcornTools.Boundary.Main, `AcornTools.Corpus.Audit, `AcornTools.Corpus.Main, `AcornTools.Boundary.Departures, `AcornTools.Corpus.Browser, `AcornTools.Corpus.Documents, `AcornTools.Corpus.Pins, `AcornTools.Gate, `AcornTools.ModuleInventory,
  `NativeApp, `NativeApp.Assets, `NativeApp.BrowserKernel,
  `NativeApp.Build, `NativeApp.Core, `NativeApp.Main, `NativeApp.Report, `NativeApp.MutationAudit,
  `Acorn.Host.Viewer.NativeResources, `AcornTools.Native.Audit,
  `AcornVerif.Resource.WordKernel,
  `AcornTools.Native.Resources, `AcornTools.Native.Routes, `NativeApp.Viewer, `AcornTools.Ownership,
  `AcornTools.OwnershipAudit, `AcornTools.TheoremCount
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
  (`Acorn.Host.AgentInterface, `Acorn.Handcrafted.Agent.callbacks_act,
    `Acorn.Handcrafted.Agent.callbacks),
  (`Acorn.Host.AgentInterface, `Acorn.Handcrafted.Agent.observe_predictions,
    `Acorn.Handcrafted.Agent.observe),
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
  (`NativeApp.MutationAudit, `NativeApp.AuditArm.incumbent_profile,
    `NativeApp.AuditArm.construction)
]

/-- Required native entry dependencies after proof erasure. These are routing
obligations; the IR graph alone does not prove control-flow or argument semantics.
Erased ANSI and checksum parameters select the compiler's reduced-arity owners. -/
def entryUses : Array (Name × Array Name) := #[
  (`NativeApp.Main, #[`NativeApp.streamingOptions, `Acorn.Host.Viewer.runNativeCampaign,
    `Acorn.Host.StopFlag.withCommands._redArg,
    `Acorn.Handcrafted.Agent.callbacks, `Acorn.Checkpoint.Store.hooks,
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
  (`AcornTools.Boundary.Main, #[`AcornBoundaryAudit.command]),
  (`AcornTools.TheoremCount, #[`AcornTheoremCount.inventory]),
  (`AcornTools.Native.Audit, #[`AcornNativeAudit.audit]),
  (`AcornTools.OwnershipAudit, #[`AcornOwnershipAudit.compiled]),
  (`AcornTools.Corpus.Main, #[`AcornCorpus.check]),
  (`AcornTools.Gate, #[`AcornGate.verify])
]

end AcornOwnership
