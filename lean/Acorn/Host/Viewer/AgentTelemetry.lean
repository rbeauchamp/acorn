/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentInterface
import Acorn.Host.Viewer.TelemetryValue

/-!
# Actual learner and decision telemetry

Each numeric array is projected from the captured learner or decision owner.
Model duration remains absent/zero in the discounted comparator. Cold decision
fields use the protocol's explicit neutral cache; no policy is sampled to fill
in missing data. Means retain the core's left-to-right binary32 arithmetic.
-/
namespace Acorn.Host.Viewer
open Features Handcrafted

/-- Closed policy-layer spellings. -/
def decisionSourceTag : TemporalSource → String
  | .primitive => "primitive"
  | .explorationStart => "exploration_start"
  | .explorationContinuation => "exploration_continuation"
  | .option _ => "option"

/-- Closed ending-reason indices match the lifetime array order. -/
def optionEndCode : OptionEnd → Nat
  | .goal => 0 | .duration => 1 | .interrupted => 2

/-- The mean follows the same ordered binary32 sum as the current diagnostic owner. -/
def meanDiagnostic {count : Nat} (values : Vector LearnerDiagnostic count) : Binary32 :=
  (Binary32.sumFrom .zero (values.toList.map (·.activeAlpha))).div
    (Binary32.ofUInt64 count.toUInt64)

private def alphaField {count : Nat} (name : String)
    (values : Vector LearnerDiagnostic count) : TelemetryField :=
  ⟨name, .array count .binary32, values.map (·.activeAlpha)⟩

private def creditField {count : Nat} (name : String)
    (values : Vector LearnerDiagnostic count) : TelemetryField :=
  ⟨name, .array count .natural, values.map (·.eligible)⟩

/-- All learner-family arrays retain the actual composition's dimensions and ordering. -/
def learnerTelemetry {config : Features.Config} {dimension : Dimension}
    (agent : AgentObservation config dimension) : List TelemetryField :=
  let learners := agent.learners
  [⟨"lifetime_step", .natural, agent.clock.toNat⟩,
   ⟨"reward_rate", .binary32, agent.gain.value⟩,
   ⟨"eps", .binary32, agent.metrics.epsilon⟩,
   ⟨"mean_alpha", .binary32, agent.metrics.meanAlpha⟩,
   ⟨"a_ctl", .binary32, meanDiagnostic learners.control⟩,
   ⟨"a_dem", .binary32, meanDiagnostic learners.demons⟩,
   alphaField "alpha_control_all" learners.control,
   alphaField "alpha_meta_all" learners.metaController,
   alphaField "alpha_option_all" learners.options.flatten,
   alphaField "alpha_demon_all" learners.demons,
   alphaField "alpha_models" learners.models.flatten,
   creditField "credit_control" learners.control,
   creditField "credit_meta" learners.metaController,
   creditField "credit_options" learners.options.flatten,
   creditField "credit_demons" learners.demons,
   creditField "credit_models" learners.models.flatten,
   ⟨"option_model_rewards", .array FeatureConstants.skillCount .binary32, agent.models.map (·.reward)⟩,
   ⟨"option_model_continuations", .array FeatureConstants.skillCount .binary32,
      agent.models.map (·.continuation)⟩,
   ⟨"option_model_durations", .array FeatureConstants.skillCount .binary32, agent.models.map (·.duration)⟩,
   ⟨"planning_errors", .array FeatureConstants.skillCount .binary32, agent.planningErrors⟩,
   ⟨"planning_steps", .natural, agent.planningSteps.toNat⟩]

/-- Decision values are the retained values that selected the actual primitive. -/
def decisionTelemetry {config : Features.Config} {dimension : Dimension}
    (agent : AgentObservation config dimension) : List TelemetryField :=
  let decision := agent.decision
  let source := decision.map (·.source) |>.getD .primitive
  let ended := decision.bind (·.ended)
  let metaDecision := decision.bind (·.metaDecision)
  [⟨"decision_source", .text, decisionSourceTag source⟩,
   ⟨"skill", .natural, match source with | .option slot => slot.val | _ => 255⟩,
   ⟨"explored", .flag, decision.any (·.explored)⟩,
   ⟨"control", .array FeatureConstants.primitiveCount .binary32,
      (decision.map (·.values)).getD (Vector.replicate _ .zero)⟩,
   ⟨"meta", .array FeatureConstants.metaActionCount .binary32,
      (decision.map (·.metaValues)).getD (Vector.replicate _ .zero)⟩,
   ⟨"action_probabilities", .array FeatureConstants.primitiveCount .binary32,
      (decision.map (·.probabilities)).getD (Vector.replicate _ .zero)⟩,
   ⟨"meta_probabilities", .array FeatureConstants.metaActionCount .binary32,
      (metaDecision.map (·.probabilities)).getD (Vector.replicate _ .zero)⟩,
   ⟨"meta_action", .natural, (metaDecision.map (·.action.val)).getD 255⟩,
   ⟨"option_start", .natural, (decision.bind (·.started) |>.map (·.val)).getD 255⟩,
   ⟨"option_end_skill", .natural, (ended.map (·.slot.val)).getD 255⟩,
   ⟨"option_end_duration", .natural, (ended.map (·.age.val)).getD 0⟩,
   ⟨"option_end_reason", .natural, (ended.map (optionEndCode ∘ (·.reason))).getD 255⟩,
   ⟨"option_elapsed", .natural, agent.optionElapsed.val⟩]

end Acorn.Host.Viewer
