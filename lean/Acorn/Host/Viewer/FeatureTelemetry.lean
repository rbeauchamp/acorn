/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentInterface
import Acorn.Host.Viewer.TelemetryValue

/-!
# Feature and prediction telemetry

Configuration and declared questions come from their existing owners. Retired
unit identity is read from the actual representation transcript, and subtask
descriptors expose stored assignments without reranking them. Cumulants reuse
the original question evaluator on the frame's observation and raw reward.
-/
namespace Acorn.Host.Viewer
open Features Handcrafted

/-- Protocol count of control, meta, option-policy and demon learners. -/
def telemetryLearnerCount : Nat :=
  FeatureConstants.primitiveCount + FeatureConstants.metaActionCount +
    FeatureConstants.skillCount * FeatureConstants.primitiveCount + FeatureConstants.demonCount

private def interestUnit {config : Features.Config} : Interest config → Option Nat
  | .declared _ _ | .learned .neutral => none
  | .learned (.selected unit _) => some unit.val

private def interestBonus {config : Features.Config} : Interest config → Binary32
  | .declared _ _ => .zero
  | .learned assignment => assignment.bonus

/-- Metadata and stored feature identities emitted by the current composition. -/
def featureTelemetry {config : Features.Config} {dimension : Dimension}
    (agent : AgentObservation config dimension) : List TelemetryField :=
  let lastRetirement := agent.representation.progress.events.getLast?
  [⟨"checkpoint_format", .natural, FeatureConstants.checkpointFormatVersion⟩,
   ⟨"control_criterion", .natural, match agent.criterion with | .discounted => 0 | .differential => 1⟩,
   ⟨"weight_space", .natural, dimension.capacity⟩,
   ⟨"primitive_count", .natural, FeatureConstants.primitiveCount⟩,
   ⟨"meta_count", .natural, FeatureConstants.metaActionCount⟩,
   ⟨"skill_count", .natural, FeatureConstants.skillCount⟩,
   ⟨"option_end_count", .natural, 3⟩,
   ⟨"demon_count", .natural, FeatureConstants.demonCount⟩,
   ⟨"learner_count", .natural, telemetryLearnerCount⟩,
   ⟨"history_bins", .natural, FeatureConstants.historyBins⟩,
   ⟨"cycle_bins", .natural, FeatureConstants.cycleBins⟩,
   ⟨"exact_cycles", .natural, FeatureConstants.exactCycles⟩,
   ⟨"settle_stride", .natural, FeatureConstants.settleStride⟩,
   ⟨"settle_remaining", .binary32, ⟨FeatureConstants.settleRemainingBits⟩⟩,
   ⟨"n_tilings", .natural, config.tilings.toNat⟩,
   ⟨"imprint_units", .natural, config.units.count⟩,
   ⟨"retire_step", .optional .natural, lastRetirement.map (·.step.toNat)⟩,
   ⟨"retire_unit", .optional .natural, lastRetirement.map (·.unit.val)⟩,
   ⟨"retire_count", .natural, agent.representation.progress.events.length⟩,
   ⟨"subtask_policy", .text, match agent.featureProfile.subtasks with
      | .learned => "learned" | .spatial => "hand_authored"⟩,
   ⟨"subtask_unit", .array FeatureConstants.skillCount (.optional .natural), agent.interests.map interestUnit⟩,
   ⟨"subtask_bonus", .array FeatureConstants.skillCount .binary32, agent.interests.map interestBonus⟩,
   ⟨"action_names", .array FeatureConstants.primitiveCount .text,
      #v["north", "south", "east", "west", "wait", "harvest", "craft_axe", "craft_boat", "eat"]⟩,
   ⟨"meta_names", .array FeatureConstants.metaActionCount .text, #v["primitive", "wood", "mine", "forage"]⟩,
   ⟨"skill_names", .array FeatureConstants.skillCount .text, #v["wood", "mine", "forage"]⟩,
   ⟨"goal_family_names", .array 4 .text, #v["reach", "collect", "craft", "survive"]⟩]

/-- Every prediction channel retains its actual cached value and declared question semantics. -/
def predictionTelemetry {config : Features.Config} {dimension : Dimension}
    (frame : StepFrame (AgentObservation config dimension)) : List TelemetryField :=
  let signals : Vector Cumulant FeatureConstants.demonCount := Vector.ofFn id
  let predictions : Vector Binary32 demonLayout.length :=
    ⟨frame.agent.predictions.words.toArray, by simpa using frame.agent.predictions.length⟩
  [⟨"demons", .array demonLayout.length .binary32, predictions⟩,
   ⟨"cums", .array FeatureConstants.demonCount .binary32,
      signals.map (fun signal => signal.eval frame.observation frame.result.reward)⟩,
   ⟨"demon_names", .array FeatureConstants.demonCount .text, signals.map Cumulant.name⟩,
   ⟨"demon_target_policy", .array FeatureConstants.demonCount .text,
      Vector.replicate _ "behavior_policy"⟩,
   ⟨"demon_gamma", .array FeatureConstants.demonCount .binary32, signals.map (fun signal => (demonDiscount signal).gamma)⟩,
   ⟨"demon_horizon", .array FeatureConstants.demonCount .binary32, signals.map (fun signal => (demonDiscount signal).horizon)⟩]

end Acorn.Host.Viewer
