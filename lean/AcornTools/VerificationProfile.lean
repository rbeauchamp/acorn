/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Lean

/-! # Explicit source profile

The tracked profile is mandatory. Bootstrap admits exactly private or public
before Lake runs. A public source tree contains exactly the selected owners;
filesystem absence never chooses a profile or suppresses a missing obligation.
-/
namespace AcornVerificationProfile
open Lean

/-- Exact tracked build/check selection, also admitted before Lake invocation. -/
def text : String := include_str "../../verification-profile"

/-- Private scientific obligations are selected explicitly. -/
def privateEvidence : Bool := text == "private\n"

/-- Private executable adapters and preparation tooling; all shared proofs remain. -/
def privateModules : Array Name := #[
  `NativeResearch,
  `NativeResearch.AverageWorker,
  `NativeResearch.AverageCommand,
  `NativeResearch.ScientificTime,
  `NativeResearch.EnduranceCommand,
  `NativeResearch.Build,
  `NativeResearch.Main,
  `NativeResearch.ExecutionIdentity,
  `NativeResearch.StudyCommand,
  `AcornStudy.Main,
  `AcornSpec.Probe,
  `AcornSpec.AgentBaselineMain,
  `AcornSpec.IntraOptionCreditMain,
  `AcornSpec.DerivedExplorationRateMain,
  `AcornSpec.StompPlanningMain,
  `AcornSpec.AverageRewardControlMain,
  `AcornTools.Corpus.Studies,
  `AcornTools.Corpus.Publication
]

/-- One source selection owns both the module and native-entry inventories. -/
def selected (owner : Name) : Bool := privateEvidence || !privateModules.contains owner

end AcornVerificationProfile
