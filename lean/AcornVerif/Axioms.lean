/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.Viewer.GoalAchievement
import Acorn.Host.Viewer.ClockProgram
import AcornVerif.AgreementLifecycle
import AcornVerif.AgreementInterpretation
import AcornVerif.CurrentBackupBounds
import AcornVerif.CurrentConstants
import AcornVerif.CurrentRetirement
import AcornVerif.CurrentRetirementRounding
import AcornVerif.Resource.WordKernel
import AcornVerif.BigWorld
import AcornVerif.Checkpoint
import AcornVerif.Energy
import AcornVerif.Exploration
import AcornVerif.MetaGradient
import AcornVerif.Options
import AcornVerif.Projection
import AcornVerif.Rng
import AcornVerif.StepSize
import AcornVerif.Traces
import AcornVerif.Retirement
import AcornVerif.AgentBaselineSemantics
import AcornVerif.StudyCompatibility
import AcornVerif.Experiment
import AcornVerif.WorldGoals
import AcornVerif.Performance
import AcornSpec.Features
import AcornVerif.Outcome
import AcornVerif.AverageReward
import AcornVerif.AverageRewardControlSemantics
import Acorn
import AcornVerif.CurrentRng
import AcornVerif.CurrentFloat
import AcornVerif.CurrentPower
import AcornVerif.CurrentExponential
import AcornVerif.CurrentArithmetic
import AcornVerif.CurrentOrder
import AcornVerif.CurrentOperations
import AcornVerif.CurrentDivision
import AcornVerif.CurrentIntervals
import AcornVerif.CurrentReduction
import AcornVerif.CurrentSeries
import AcornVerif.CurrentPortable
import AcornVerif.CurrentLogarithm
import AcornVerif.CurrentPrediction
import AcornVerif.CurrentState
import AcornVerif.CurrentLearnerArithmetic
import AcornVerif.CurrentLearner
import AcornVerif.CurrentControl
import AcornVerif.CurrentAgent
import AcornVerif.CurrentCheckpoint
import AcornVerif.CurrentModels
import AcornVerif.CurrentTemporal
import AcornVerif.TemporalSupport
import AcornVerif.CurrentFloor
import AcornVerif.CurrentWorld
import AcornVerif.CurrentRunner
import AcornVerif.Endurance

/-!
# Axiom audit

The complete theorem inventory admits only dependencies on `propext`,
`Classical.choice` and `Quot.sound`. Source and compiled admission reject
project-owned axioms and unchecked native proof replacements. The guards below
pin the exact dependency sets of selected named theorems.

`#guard_msgs` makes it a build failure: if an `axiom` is introduced, or an
import starts dragging one in, the message printed by `#print axioms` changes
and this file stops compiling. These retained exact-set guards complement
`theorem-count`, which uses compiler module ownership to audit every maintained
public, private and generated theorem's transitive axioms against the same
three-name allowlist. New declarations cannot bypass that inventory through
namespace aliases or source formatting.

A `sorry` is caught by a different mechanism: `warningAsError := true` in
`lakefile.lean` turns "declaration uses `sorry`" into a build failure before
this file is even elaborated. Credit where it is due — `#guard_msgs` covers
axioms, the lakefile covers `sorry`.

There are no unit tests in this project; the compiler is the whole safety net,
and this is the compiler checking the soundness claim.
-/

namespace AcornVerif

-- This file's entire purpose is `#print axioms`, so Mathlib's ban on
-- `#`-commands does not apply to it.
set_option linter.hashCommand false

/--
info: 'Acorn.Host.Viewer.GoalAchievement.State.observe_resolution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Acorn.Host.Viewer.GoalAchievement.State.observe_resolution

/--
info: 'Acorn.Host.Viewer.GoalAchievement.Pass.permille_precision' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Acorn.Host.Viewer.GoalAchievement.Pass.permille_precision

/--
info: 'Acorn.Host.Viewer.ClockProgram.snapshotFollows_goal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Acorn.Host.Viewer.ClockProgram.snapshotFollows_goal

/--
info: 'AcornVerif.AgreementLifecycle.observe_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AcornVerif.AgreementLifecycle.observe_invariant

/--
info: 'AcornVerif.AgreementLifecycle.settlement_available' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AcornVerif.AgreementLifecycle.settlement_available

/--
info: 'AcornVerif.CurrentAgreement.aggregateAll_value' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AcornVerif.CurrentAgreement.aggregateAll_value

/--
info: 'AcornVerif.AgreementPrecision.agreement_precision' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AcornVerif.AgreementPrecision.agreement_precision

/--
info: 'AcornVerif.AgreementInterpretation.conditional_mean_minimizes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AcornVerif.AgreementInterpretation.conditional_mean_minimizes

/--
info: 'AcornVerif.AgreementTelemetryPrecision.precision_available' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AcornVerif.AgreementTelemetryPrecision.precision_available

/-- info: 'Acorn.Binary32.finite_not_nan' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Binary32.finite_not_nan

/-- info: 'Acorn.Binary32.less_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Binary32.less_finite

/-- info: 'Acorn.Interval32.interval_admit_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Interval32.interval_admit_exact

/-- info: 'Acorn.Interval32.interval_admit_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Interval32.interval_admit_refuses

/-- info: 'Acorn.Interval32.finite_between' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Interval32.finite_between

/-- info: 'Acorn.Interval32.saturate_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Interval32.saturate_contains

/-- info: 'Acorn.Interval32.saturate_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Interval32.saturate_identity

/-- info: 'Acorn.Interval32.saturate_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Interval32.saturate_idempotent

/-- info: 'Acorn.Bounded32.admit_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Bounded32.admit_exact

/-- info: 'Acorn.Bounded32.admit_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Bounded32.admit_refuses

/-- info: 'AcornVerif.differential_error_shift' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_error_shift

/-- info: 'AcornVerif.differential_error_offset_mismatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_error_offset_mismatch

/-- info: 'AcornVerif.differential_return_duration' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_return_duration

/-- info: 'AcornVerif.differential_return_rate_change' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_return_rate_change

/-- info: 'AcornVerif.two_state_differential_rate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_state_differential_rate

/-- info: 'AcornVerif.two_state_differential_span' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_state_differential_span

/-- info: 'AcornVerif.two_state_centered_solution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_state_centered_solution

/-- info: 'AcornVerif.two_state_span_exceeds_budget' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_state_span_exceeds_budget

/-- info: 'AcornVerif.reward_rate_step_convex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reward_rate_step_convex

/-- info: 'AcornVerif.reward_rate_step_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reward_rate_step_bounded

/-- info: 'AcornVerif.reward_rate_constant_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reward_rate_constant_error

/-- info: 'AcornVerif.differential_model_gain_correction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_model_gain_correction

/-- info: 'AcornVerif.differential_backup_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_backup_distance

/-- info: 'AcornVerif.differential_policy_target_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_policy_target_discrepancy

/-- info: 'AcornVerif.differential_optimistic_backup_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_optimistic_backup_residual

/-- info: 'AcornVerif.differential_optimistic_backup_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_optimistic_backup_positive

/-- info: 'AcornVerif.differential_projected_backup_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_projected_backup_discrepancy

/-- info: 'AcornVerif.differential_projected_backup_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_projected_backup_agrees

/-- info: 'AcornVerif.differential_projected_gain_discrepancy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_projected_gain_discrepancy

/-- info: 'AcornVerif.differential_expected_duration_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differential_expected_duration_zero_iff

/-- info: 'AcornVerif.option_model_terminal_discount_correction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms option_model_terminal_discount_correction

/-- info: 'AcornVerif.historical_domain_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms historical_domain_identity

/-- info: 'AcornVerif.historical_stream_identity' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms historical_stream_identity

/-- info: 'AcornVerif.historical_analysis_identity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms historical_analysis_identity

/-- info: 'AcornVerif.baseline_acceptance_flags' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms baseline_acceptance_flags

/-- info: 'AcornVerif.baseline_acceptance_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms baseline_acceptance_iff

/-- info: 'AcornVerif.horizon_covers_true_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms horizon_covers_true_bound

/-- info: 'AcornVerif.gamma_is_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gamma_is_contraction

/-- info: 'AcornVerif.project_nonexpansive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms project_nonexpansive

/-- info: 'AcornVerif.project_mem_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms project_mem_range

/-- info: 'AcornVerif.project_id_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms project_id_of_mem

/-- info: 'AcornVerif.next_below_in_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_below_in_range

/-- info: 'AcornVerif.natCeilDiv_le_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms natCeilDiv_le_iff

/-- info: 'AcornVerif.lt_natCeilDiv_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lt_natCeilDiv_iff

/-- info: 'AcornVerif.next_below_bin_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms next_below_bin_iff

/-- info: 'AcornVerif.next_below_bin_eq_Ico' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_below_bin_eq_Ico

/-- info: 'AcornVerif.next_below_bin_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_below_bin_card

/-- info: 'AcornVerif.natCeilDiv_add_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms natCeilDiv_add_sub

/-- info: 'AcornVerif.next_below_bins_within_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_below_bins_within_one

/-- info: 'AcornVerif.next_below_word_bins_within_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms next_below_word_bins_within_one

/-- info: 'AcornVerif.step_size_pos_after_clip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_size_pos_after_clip

/-- info: 'AcornVerif.trace_geometric_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_geometric_bound

/-- info: 'AcornVerif.big_world_margin_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms big_world_margin_holds

/-- info: 'AcornVerif.agent_exceeds_terrain_description' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agent_exceeds_terrain_description

/-- info: 'AcornVerif.stepPaper_eq_eq32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepPaper_eq_eq32

/-- info: 'AcornVerif.stepRef_hTemp_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepRef_hTemp_error

/-- info: 'AcornVerif.metaTrace_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms metaTrace_lag

/-- info: 'AcornVerif.exhaustion_rate_at_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exhaustion_rate_at_build

/-- info: 'AcornVerif.constant_cumulant_fixed_point_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms constant_cumulant_fixed_point_unique

/-- info: 'AcornVerif.step_size_upper_after_clip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_size_upper_after_clip

/-- info: 'AcornVerif.step_size_lower_after_clip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms step_size_lower_after_clip

/-- info: 'AcornVerif.total_trace_increment_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms total_trace_increment_bounded

/-- info: 'AcornVerif.trace_increment_le_step_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_increment_le_step_size

/-- info: 'AcornVerif.decay_shrinks_step_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms decay_shrinks_step_size

/-- info: 'AcornVerif.trace_decay_monotone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms trace_decay_monotone

/-- info: 'AcornVerif.pruning_implies_negligible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pruning_implies_negligible

/-- info: 'AcornVerif.theta_eq_epsilon_div_one_sub_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms theta_eq_epsilon_div_one_sub_gamma

/-- info: 'AcornVerif.prediction_change_eq_abs_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms prediction_change_eq_abs_weight

/-- info: 'AcornVerif.relative_disruption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms relative_disruption

/-- info: 'AcornVerif.every_consumer_prediction_change' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms every_consumer_prediction_change

/-- info: 'AcornVerif.Retirement.admitsFrom_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Retirement.admitsFrom_iff

/-- info: 'AcornVerif.Retirement.transcript_admission_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Retirement.transcript_admission_iff

/-- info: 'AcornVerif.Retirement.clock_advance_preserves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Retirement.clock_advance_preserves

/-- info: 'AcornVerif.Retirement.append_admission_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Retirement.append_admission_iff

/-- info: 'AcornVerif.Retirement.finalStep_eq_last' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Retirement.finalStep_eq_last

/-- info: 'AcornVerif.Retirement.record_preserves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Retirement.record_preserves

/-- info: 'AcornVerif.exhausted_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exhausted_bound

/-- info: 'AcornVerif.exhaustion_rate_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exhaustion_rate_bound

/-- info: 'AcornVerif.rest_pays_for_an_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rest_pays_for_an_action

/-- info: 'AcornVerif.every_action_costs' depends on axioms: [propext] -/
#guard_msgs in
#print axioms every_action_costs

/-- info: 'AcornVerif.stepPaper_shifts_lags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepPaper_shifts_lags

/-- info: 'AcornVerif.stepRef_h_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stepRef_h_error

/-- info: 'AcornVerif.metaGain_at_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms metaGain_at_floor

/-- info: 'AcornVerif.metaGain_strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms metaGain_strictAnti

/-- info: 'AcornVerif.metaGainStabilised_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms metaGainStabilised_le

/-- info: 'AcornVerif.beta_floor_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms beta_floor_reachable

/-- info: 'AcornVerif.beta_floor_absorbing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms beta_floor_absorbing

/-- info: 'AcornVerif.constant_cumulant_fixed_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms constant_cumulant_fixed_point

/-- info: 'AcornVerif.run_realizes_eq32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms run_realizes_eq32

/-- info: 'AcornVerif.one_le_floor_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_le_floor_inv

/-- info: 'AcornVerif.ez_duration_le_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ez_duration_le_cap

/-- info: 'AcornVerif.ez_duration_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ez_duration_pos

/-- info: 'AcornVerif.ez_contains_epsilon_greedy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ez_contains_epsilon_greedy

/-- info: 'AcornVerif.ez_remaining_zero_at_cap_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ez_remaining_zero_at_cap_one

/-- info: 'AcornVerif.ez_duration_le_shipped_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ez_duration_le_shipped_cap

/-- info: 'AcornVerif.terminal_correction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms terminal_correction

/-- info: 'AcornVerif.nonterminal_bellman_correction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nonterminal_bellman_correction

/-- info: 'AcornVerif.finite_activation_bootstrap_correction' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_activation_bootstrap_correction

/-- info: 'AcornVerif.subtask_returns_agree' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subtask_returns_agree

/-- info: 'AcornVerif.finite_activation_correction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms finite_activation_correction

/-- info: 'AcornVerif.corrected_interruption_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corrected_interruption_iff

/-- info: 'AcornVerif.controller_discounts_match' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms controller_discounts_match

/-- info: 'AcornVerif.gap_close_is_smdp_backup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms gap_close_is_smdp_backup

/-- info: 'AcornVerif.subtask_terminal_telescoping' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subtask_terminal_telescoping

/-- info: 'AcornVerif.subtask_potential_invariance' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subtask_potential_invariance

/-- info: 'AcornVerif.subtask_block_exclusivity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms subtask_block_exclusivity

/-- info: 'AcornVerif.option_model_scalar_continuation_equiv' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms option_model_scalar_continuation_equiv

/-- info: 'AcornVerif.option_model_termination_telescoping' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms option_model_termination_telescoping

/-- info: 'AcornVerif.stomp_planning_backup_contraction' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stomp_planning_backup_contraction

/-- info: 'AcornVerif.planning_weight_convex_step_bounded' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms planning_weight_convex_step_bounded

/-- info: 'AcornVerif.study_goal_cap_is_derived' depends on axioms: [propext] -/
#guard_msgs in
#print axioms study_goal_cap_is_derived

/-- info: 'AcornVerif.study_seed_population_is_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms study_seed_population_is_closed

/-- info: 'AcornVerif.study_seed_population_is_nodup' does not depend on any axioms -/
#guard_msgs in
#print axioms study_seed_population_is_nodup

/-- info: 'AcornVerif.study_arm_domain_is_closed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms study_arm_domain_is_closed

/-- info: 'AcornVerif.goal_efficiency_mem_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms goal_efficiency_mem_unit

/-- info: 'AcornVerif.goal_efficiency_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms goal_efficiency_failure

/-- info: 'AcornVerif.reach_capped_time_failure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms reach_capped_time_failure

/-- info: 'AcornVerif.reach_capped_time_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reach_capped_time_bounds

/-- info: 'AcornVerif.goal_efficiency_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms goal_efficiency_antitone

/-- info: 'AcornVerif.goal_efficiency_strict_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms goal_efficiency_strict_antitone

/-- info: 'AcornVerif.primary_eligibility_symmetric' depends on axioms: [propext] -/
#guard_msgs in
#print axioms primary_eligibility_symmetric

/-- info: 'AcornVerif.win_credit_mem_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms win_credit_mem_unit

/-- info: 'AcornVerif.rational_sum_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational_sum_bounds

/-- info: 'AcornVerif.rational_mean_mem_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational_mean_mem_unit

/-- info: 'AcornVerif.stratified_score_mem_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms stratified_score_mem_unit

/-- info: 'AcornVerif.every_arm_has_equal_opportunity' does not depend on any axioms -/
#guard_msgs in
#print axioms every_arm_has_equal_opportunity

/-- info: 'AcornVerif.arm_semantics_match_rust' does not depend on any axioms -/
#guard_msgs in
#print axioms arm_semantics_match_rust

/-- info: 'AcornVerif.frozen_is_exact_learning_ablation' does not depend on any axioms -/
#guard_msgs in
#print axioms frozen_is_exact_learning_ablation

/-- info: 'AcornVerif.goal_relation_is_exact_ablation' does not depend on any axioms -/
#guard_msgs in
#print axioms goal_relation_is_exact_ablation

/-- info: 'AcornVerif.temporal_abstraction_is_exact_ablation' does not depend on any axioms -/
#guard_msgs in
#print axioms temporal_abstraction_is_exact_ablation

/-- info: 'AcornVerif.final_frozen_initialization_is_identical' does not depend on any axioms -/
#guard_msgs in
#print axioms final_frozen_initialization_is_identical

/-- info: 'AcornVerif.agent_initialization_is_world_seed_independent' does not depend on any axioms -/
#guard_msgs in
#print axioms agent_initialization_is_world_seed_independent

/-- info: 'AcornVerif.frozen_transition_preserves_learning' does not depend on any axioms -/
#guard_msgs in
#print axioms frozen_transition_preserves_learning

/-- info: 'AcornVerif.structural_config_is_seed_independent' does not depend on any axioms -/
#guard_msgs in
#print axioms structural_config_is_seed_independent

/-- info: 'AcornVerif.reach_remaining_zero_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms reach_remaining_zero_iff

/-- info: 'AcornVerif.collect_remaining_zero_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms collect_remaining_zero_iff

/-- info: 'AcornVerif.craft_remaining_zero_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms craft_remaining_zero_iff

/-- info: 'AcornVerif.survive_remaining_zero_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms survive_remaining_zero_iff

/-- info: 'AcornVerif.goal_remaining_zero_iff_satisfied' depends on axioms: [propext] -/
#guard_msgs in
#print axioms goal_remaining_zero_iff_satisfied

/-- info: 'AcornVerif.chebyshev_reduces_when_x_reduces' depends on axioms: [propext] -/
#guard_msgs in
#print axioms chebyshev_reduces_when_x_reduces

/-- info: 'AcornVerif.fieldwise_result_envelope_has_every_coordinate_combination' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms fieldwise_result_envelope_has_every_coordinate_combination

/-- info: 'AcornVerif.agent_baseline_acceptance_iff_outcomes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms agent_baseline_acceptance_iff_outcomes

/-- info: 'AcornVerif.performance_certificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms performance_certificate_sound

/-- info: 'AcornVerif.required_win_units_at_build' depends on axioms: [propext] -/
#guard_msgs in
#print axioms required_win_units_at_build

/-- info: 'AcornVerif.paired_probability_threshold_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paired_probability_threshold_iff

/-- info: 'AcornVerif.study_max_transitions_at_build' depends on axioms: [propext] -/
#guard_msgs in
#print axioms study_max_transitions_at_build

/-- info: 'AcornVerif.paired_point_futility' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms paired_point_futility

/-- info: 'AcornVerif.paired_probability_futility' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms paired_probability_futility

/-- info: 'AcornVerif.winCredit_eq_registered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms winCredit_eq_registered

/-- info: 'AcornVerif.tally_record_seeds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tally_record_seeds

/-- info: 'AcornVerif.tally_record_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tally_record_credit

/-- info: 'AcornVerif.tally_foldl_seeds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tally_foldl_seeds

/-- info: 'AcornVerif.tally_foldl_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tally_foldl_credit

/-- info: 'AcornVerif.tally_partitions' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tally_partitions

/-- info: 'AcornVerif.foldl_add_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms foldl_add_eq_sum

/-- info: 'AcornVerif.tally_poi_eq_mean_credit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms tally_poi_eq_mean_credit

/-- info: 'AcornVerif.pairedSummary_poi_is_tally' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms pairedSummary_poi_is_tally
-- The executable specification's own theorems (`AcornSpec/Features.lean`):
-- the unique pass, its packed-word mirror, and the equivalence between them.

/-- info: 'AcornSpec.Featurizer.firstOccurrences_sublist' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.firstOccurrences_sublist

/-- info: 'AcornSpec.Featurizer.firstOccurrences_not_mem_seen' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.firstOccurrences_not_mem_seen

/-- info: 'AcornSpec.Featurizer.firstOccurrences_nodup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.firstOccurrences_nodup

/-- info: 'AcornSpec.Featurizer.wordOf_lt' does not depend on any axioms -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.wordOf_lt

/-- info: 'AcornSpec.Featurizer.and_two_pow_ne_zero_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.and_two_pow_ne_zero_iff

/-- info: 'AcornSpec.Featurizer.uint64_ne_zero_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.uint64_ne_zero_iff

/-- info: 'AcornSpec.Featurizer.toNat_bitOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.toNat_bitOf

/-- info: 'AcornSpec.Featurizer.wordOf_eq_div' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.wordOf_eq_div

/-- info: 'AcornSpec.Featurizer.seenBit_markSeen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.seenBit_markSeen

/-- info: 'AcornSpec.Featurizer.not_seenBit_replicate_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.not_seenBit_replicate_zero

/-- info: 'AcornSpec.Featurizer.foldl_uniqueStep_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.foldl_uniqueStep_eq

/-- info: 'AcornSpec.Featurizer.uniqueIndices_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.uniqueIndices_eq

/-- info: 'AcornSpec.Featurizer.uniqueIndices_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.uniqueIndices_nodup

/-- info: 'AcornSpec.Featurizer.uniqueIndices_sublist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.uniqueIndices_sublist

/-- info: 'AcornSpec.Featurizer.mask_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.mask_lt

/-- info: 'AcornSpec.Featurizer.encodeWordsGo_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.encodeWordsGo_lt

/-- info: 'AcornSpec.Featurizer.encodeTilingsGo_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.encodeTilingsGo_lt

/-- info: 'AcornSpec.Featurizer.imprintPush_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.imprintPush_lt

/-- info: 'AcornSpec.Featurizer.imprintUnitsGo_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.imprintUnitsGo_lt

/-- info: 'AcornSpec.Featurizer.rawEncode_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.rawEncode_lt

/-- info: 'AcornSpec.Featurizer.encode_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.encode_nodup

/-- info: 'AcornSpec.Featurizer.encode_sublist_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornSpec.Featurizer.encode_sublist_raw

/-- info: 'AcornVerif.AverageRewardControlSemantics.successes_le_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.successes_le_length
/-- info: 'AcornVerif.AverageRewardControlSemantics.complete_goals_exposure' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.complete_goals_exposure
/-- info: 'AcornVerif.AverageRewardControlSemantics.admitted_cycle_exposure' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.admitted_cycle_exposure
/-- info: 'AcornVerif.AverageRewardControlSemantics.admitted_cycle_latency' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.admitted_cycle_latency
/-- info: 'AcornVerif.AverageRewardControlSemantics.supported_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.supported_iff
/-- info: 'AcornVerif.AverageRewardControlSemantics.refuted_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.refuted_iff
/-- info: 'AcornVerif.AverageRewardControlSemantics.assessment_labels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.assessment_labels
/-- info: 'AcornVerif.AverageRewardControlSemantics.complete_report_population' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.complete_report_population

/-- info: 'AcornVerif.capped_fold_invariant' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.capped_fold_invariant

/-- info: 'AcornVerif.active_features_count_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.active_features_count_bound

/-- info: 'AcornVerif.with_model_feature_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.with_model_feature_nodup

/-- info: 'AcornVerif.with_model_feature_preserves' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.with_model_feature_preserves

/-- info: 'AcornVerif.with_model_feature_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.with_model_feature_length

/-- info: 'AcornVerif.ema_horizon_mean_age' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.ema_horizon_mean_age

/-- info: 'AcornVerif.ema_horizon_squared_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.ema_horizon_squared_mass


/-- info: 'AcornVerif.AverageRewardControlSemantics.admitted_process_peak' does not depend on any axioms -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.admitted_process_peak

/-- info: 'AcornVerif.AverageRewardControlSemantics.factorial_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.factorial_correct

/-- info: 'AcornVerif.AverageRewardControlSemantics.binomial_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.binomial_correct

/-- info: 'AcornVerif.AverageRewardControlSemantics.binomial_pascal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.binomial_pascal

/-- info: 'AcornVerif.AverageRewardControlSemantics.revision_sign_threshold' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.revision_sign_threshold

/-- info: 'AcornVerif.AverageRewardControlSemantics.revision_large_effect_resolution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.revision_large_effect_resolution

/-- info: 'AcornVerif.AverageRewardControlSemantics.admitted_invocation_complete' does not depend on any axioms -/
#guard_msgs in
#print axioms AcornVerif.AverageRewardControlSemantics.admitted_invocation_complete

/-- info: 'AcornVerif.Checkpoint.identity_accepted_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Checkpoint.identity_accepted_iff

/-- info: 'AcornVerif.Checkpoint.identity_mismatch_refused' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Checkpoint.identity_mismatch_refused

/-- info: 'AcornVerif.Checkpoint.commit_assignment' does not depend on any axioms -/
#guard_msgs in
#print axioms Checkpoint.commit_assignment

/-- info: 'AcornVerif.Checkpoint.commit_primary' does not depend on any axioms -/
#guard_msgs in
#print axioms Checkpoint.commit_primary

/-- info: 'AcornVerif.Checkpoint.commit_pair' does not depend on any axioms -/
#guard_msgs in
#print axioms Checkpoint.commit_pair

/-- info: 'AcornVerif.Checkpoint.commit_identity' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Checkpoint.commit_identity

/-- info: 'AcornVerif.Checkpoint.refusal_unchanged' does not depend on any axioms -/
#guard_msgs in
#print axioms Checkpoint.refusal_unchanged

/-- info: 'AcornVerif.Checkpoint.restore_admitted' does not depend on any axioms -/
#guard_msgs in
#print axioms Checkpoint.restore_admitted

/-- info: 'AcornVerif.Checkpoint.appended_name_longer' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Checkpoint.appended_name_longer

/-- info: 'AcornVerif.Checkpoint.appended_name_ne' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Checkpoint.appended_name_ne

/-- info: 'AcornVerif.Checkpoint.writes_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Checkpoint.writes_iff

/-- info: 'AcornVerif.Checkpoint.due_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Checkpoint.due_iff

/-- info: 'AcornVerif.Checkpoint.refused_never_writes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Checkpoint.refused_never_writes

/-- info: 'AcornVerif.Checkpoint.load_only_never_writes' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Checkpoint.load_only_never_writes

/-- info: 'AcornVerif.Checkpoint.stop_permission_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Checkpoint.stop_permission_iff

/-- info: 'AcornVerif.Checkpoint.campaign_goals_exact' does not depend on any axioms -/
#guard_msgs in
#print axioms Checkpoint.campaign_goals_exact

/-- info: 'AcornVerif.Checkpoint.campaign_unbounded_nonempty' does not depend on any axioms -/
#guard_msgs in
#print axioms Checkpoint.campaign_unbounded_nonempty

/-- info: 'AcornVerif.Checkpoint.campaign_finite_accepted' does not depend on any axioms -/
#guard_msgs in
#print axioms Checkpoint.campaign_finite_accepted

/-- info: 'AcornVerif.Checkpoint.campaign_empty_accepted_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Checkpoint.campaign_empty_accepted_iff

/-- info: 'AcornVerif.Refresh.busy_preserves' does not depend on any axioms -/
#guard_msgs in
#print axioms Refresh.busy_preserves

/-- info: 'AcornVerif.Refresh.idle_completes' does not depend on any axioms -/
#guard_msgs in
#print axioms Refresh.idle_completes

/-- info: 'AcornVerif.Refresh.conservation' does not depend on any axioms -/
#guard_msgs in
#print axioms Refresh.conservation

/-- info: 'AcornVerif.Refresh.exclusive' does not depend on any axioms -/
#guard_msgs in
#print axioms Refresh.exclusive

/-- info: 'AcornVerif.Refresh.coalesces' does not depend on any axioms -/
#guard_msgs in
#print axioms Refresh.coalesces

/-- info: 'AcornVerif.Refresh.request_preserves' does not depend on any axioms -/
#guard_msgs in
#print axioms Refresh.request_preserves

/-- info: 'AcornVerif.Refresh.busy_stream_exact' does not depend on any axioms -/
#guard_msgs in
#print axioms Refresh.busy_stream_exact

/-- info: 'AcornVerif.Refresh.first_idle_exact' does not depend on any axioms -/
#guard_msgs in
#print axioms Refresh.first_idle_exact

/-- info: 'AcornVerif.Refresh.replacement_exact' does not depend on any axioms -/
#guard_msgs in
#print axioms Refresh.replacement_exact

/-- info: 'AcornVerif.Refresh.closing_owner_exact' does not depend on any axioms -/
#guard_msgs in
#print axioms Refresh.closing_owner_exact

/-- info: 'AcornVerif.Refresh.continuation_exact' does not depend on any axioms -/
#guard_msgs in
#print axioms Refresh.continuation_exact

/-- info: 'AcornVerif.Refresh.replaced_credit_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Refresh.replaced_credit_zero

/-- info: 'AcornVerif.Refresh.unchanged_credit_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Refresh.unchanged_credit_exact

/-- info: 'Acorn.Symmetric32.symmetric_project_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Symmetric32.symmetric_project_contains

/-- info: 'Acorn.Symmetric32.symmetric_project_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Symmetric32.symmetric_project_identity

/-- info: 'Acorn.Symmetric32.symmetric_project_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Symmetric32.symmetric_project_idempotent

/-- info: 'Acorn.Binary32.sumFrom_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Binary32.sumFrom_append

/-- info: 'Acorn.Binary64.hornerFrom_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Binary64.hornerFrom_append

/-- info: 'Acorn.Bounded32.addProjected_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Bounded32.addProjected_legal

/-- info: 'Acorn.average_observe_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.average_observe_legal

/-- info: 'Acorn.average_restore_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.average_restore_word

/-- info: 'Acorn.average_observe_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.average_observe_append

/-- info: 'Acorn.Conversion.clampInt_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.clampInt_bounds

/-- info: 'Acorn.Conversion.signedCast_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.signedCast_bounds

/-- info: 'Acorn.Portable.exp_nan_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Portable.exp_nan_word

/-- info: 'Acorn.Portable.powLoop_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Portable.powLoop_zero

/-- info: 'Acorn.Portable.powLoop_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Portable.powLoop_step

/-- info: 'Acorn.Rng.splitmix_two_offsets' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.splitmix_two_offsets

/-- info: 'Acorn.Rng.nextBelow_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.nextBelow_transition

/-- info: 'Acorn.Rng.nextBelow_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.nextBelow_quotient

/-- info: 'Acorn.Rng.nextF64_transition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.nextF64_transition

/-- info: 'Acorn.Rng.prefix_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.prefix_length

/-- info: 'Acorn.Rng.prefix_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.prefix_state

/-- info: 'Acorn.Rng.prefix_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.prefix_append

/-- info: 'Acorn.Rng.prefix_zero_state' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.prefix_zero_state

/-- info: 'Acorn.Rng.fnvStep_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.fnvStep_injective

/-- info: 'Acorn.Rng.fnv_append' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.fnv_append

/-- info: 'Acorn.Rng.state_rotation_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.state_rotation_injective

/-- info: 'Acorn.Rng.next_state_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.next_state_injective

/-- info: 'Acorn.Rng.word_right_xor_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.word_right_xor_injective

/-- info: 'Acorn.Rng.mixFinal_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.mixFinal_injective

/-- info: 'Acorn.Rng.mix64_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.mix64_injective

/-- info: 'Acorn.Rng.advance_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.advance_injective

/-- info: 'Acorn.Rng.advance_nonzero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.advance_nonzero

/-- info: 'Acorn.Rng.seed_nonzero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.seed_nonzero

/-- info: 'Acorn.Rounding.nearestEven_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rounding.nearestEven_distance

/-- info: 'Acorn.Rounding.nearestEven_tie' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rounding.nearestEven_tie

/-- info: 'Acorn.Rounding.nearestEven_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Acorn.Rounding.nearestEven_exact

/-- info: 'Acorn.Rounding.nearestEven_le_input' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rounding.nearestEven_le_input

/-- info: 'Acorn.Rounding.nearestEven_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rounding.nearestEven_bracket

/-- info: 'Acorn.Rounding.wordShift_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rounding.wordShift_exact

/-- info: 'Acorn.Rounding.wordShift_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rounding.wordShift_distance

/-- info: 'Acorn.Rounding.wordShift_carry_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rounding.wordShift_carry_bound

/-- info: 'Acorn.Rounding.wordShift_leading_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rounding.wordShift_leading_bit

/-- info: 'Acorn.Rng.countOfNat_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Acorn.Rng.countOfNat_exact

/-- info: 'Acorn.Rng.shuffleLoop_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.shuffleLoop_state

/-- info: 'Acorn.Rng.shuffleLoop_permutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rng.shuffleLoop_permutation

/-- info: 'Acorn.rails_admission_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.rails_admission_total

/-- info: 'Acorn.feature_index_word_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Acorn.feature_index_word_exact

/-- info: 'Acorn.Word.multiplier_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Acorn.Word.multiplier_injective

/-- info: 'Acorn.Word.xor_word_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Word.xor_word_injective

/-- info: 'Acorn.Word.product_fits' does not depend on any axioms -/
#guard_msgs in
#print axioms Acorn.Word.product_fits

/-- info: 'Acorn.Word.high_fits' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Acorn.Word.high_fits

/-- info: 'Acorn.Word.multiplyHigh_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Word.multiplyHigh_exact

/-- info: 'Acorn.Word.multiplyHigh_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Word.multiplyHigh_below

/-- info: 'Acorn.Word.clock_advance_exact' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Acorn.Word.clock_advance_exact

/-- info: 'Acorn.Word.clock_advance_refuses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Acorn.Word.clock_advance_refuses

/-- info: 'Acorn.Word.xor_shiftLeft_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Word.xor_shiftLeft_injective

/-- info: 'Acorn.Word.rotate_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Word.rotate_injective

/-- info: 'Acorn.Word.xor_shiftRight_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Word.xor_shiftRight_injective

/-- info: 'AcornVerif.current_range_bin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.current_range_bin

/-- info: 'AcornVerif.current_range_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.current_range_word

/-- info: 'AcornVerif.current_range_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.current_range_card

/-- info: 'Acorn.Conversion.normalSignificand_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalSignificand_bounds

/-- info: 'Acorn.Conversion.roundedNormal_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.roundedNormal_bounds

/-- info: 'Acorn.Conversion.normalizedNormal_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalizedNormal_bounds

/-- info: 'Acorn.Conversion.normalizedNormal_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalizedNormal_value

/-- info: 'Acorn.Conversion.normalFraction_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalFraction_exact

/-- info: 'Acorn.Conversion.normalFraction_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalFraction_distance

/-- info: 'Acorn.Conversion.subnormalShift_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.subnormalShift_lower

/-- info: 'Acorn.Conversion.subnormalSignificand_upper' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.subnormalSignificand_upper

/-- info: 'Acorn.Conversion.subnormalFraction_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.subnormalFraction_exact

/-- info: 'Acorn.Conversion.subnormalFraction_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.subnormalFraction_distance

/-- info: 'Acorn.Conversion.subnormalFraction_tie' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.subnormalFraction_tie

/-- info: 'Acorn.Conversion.normalFields_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalFields_exact

/-- info: 'Acorn.Conversion.narrowSign_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrowSign_exact

/-- info: 'Acorn.Conversion.narrowSign_magnitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrowSign_magnitude

/-- info: 'Acorn.Conversion.normalExponent_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalExponent_bounds

/-- info: 'Acorn.Conversion.normalMagnitude_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalMagnitude_bound

/-- info: 'Acorn.Conversion.narrow_finite_input_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_finite_input_bound

/-- info: 'Acorn.Conversion.normalFraction_tie' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalFraction_tie

/-- info: 'Acorn.Conversion.narrowSign_highBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrowSign_highBit

/-- info: 'Acorn.Conversion.normalExponent_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalExponent_exact

/-- info: 'Acorn.Conversion.normalMagnitude_finite_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalMagnitude_finite_iff

/-- info: 'Acorn.Conversion.widenSubnormalFraction_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widenSubnormalFraction_exact

/-- info: 'Acorn.Conversion.widenSubnormalFraction_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widenSubnormalFraction_value

/-- info: 'Acorn.Conversion.widenSubnormalFraction_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widenSubnormalFraction_bound

/-- info: 'Acorn.Conversion.widenFraction_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widenFraction_exact

/-- info: 'Acorn.Conversion.wideFields_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.wideFields_exact

/-- info: 'Acorn.Conversion.widenSign_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widenSign_exact

/-- info: 'Acorn.Conversion.widenSign_magnitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widenSign_magnitude

/-- info: 'Acorn.Conversion.widenSign_highBit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widenSign_highBit

/-- info: 'Acorn.Conversion.fields32_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.fields32_decomposition

/-- info: 'Acorn.Conversion.fields32_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.fields32_bounds

/-- info: 'Acorn.Conversion.fields32_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.fields32_units

/-- info: 'Acorn.Conversion.wideFields_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.wideFields_units

/-- info: 'Acorn.Conversion.wideFields_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.wideFields_finite

/-- info: 'Acorn.Conversion.wideFields_sign' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.wideFields_sign

/-- info: 'Acorn.Conversion.narrowFields_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrowFields_units

/-- info: 'Acorn.Conversion.subnormalFields_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.subnormalFields_units

/-- info: 'Acorn.Conversion.fields64_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.fields64_decomposition

/-- info: 'Acorn.Conversion.fraction64_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.fraction64_bound

/-- info: 'Acorn.Conversion.normalSignificand_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalSignificand_value

/-- info: 'Acorn.Conversion.fields64_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.fields64_units

/-- info: 'Acorn.Conversion.fields64_scaled_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.fields64_scaled_units

/-- info: 'Acorn.Conversion.subnormalScale_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.subnormalScale_exact

/-- info: 'Acorn.Conversion.normalMagnitude_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalMagnitude_units

/-- info: 'Acorn.Conversion.normalExponent_scale' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalExponent_scale

/-- info: 'Acorn.Conversion.normalMagnitude_rounded_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalMagnitude_rounded_units

/-- info: 'Acorn.Conversion.normalMagnitude_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalMagnitude_distance

/-- info: 'Acorn.Conversion.subnormalMagnitude_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.subnormalMagnitude_distance

/-- info: 'Acorn.Conversion.widen_magnitude_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widen_magnitude_exact

/-- info: 'Acorn.Conversion.widen_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widen_finite

/-- info: 'Acorn.Conversion.narrow_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_sign

/-- info: 'Acorn.Conversion.narrow_finite_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_finite_iff

/-- info: 'Acorn.Conversion.narrow_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_distance

/-- info: 'Acorn.Conversion.widen_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widen_sign

/-- info: 'Acorn.Conversion.narrow_finite_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_finite_distance

/-- info: 'Acorn.Conversion.trunc64_magnitude_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.trunc64_magnitude_exact

/-- info: 'Acorn.Rounding.nearestEven_scaled_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rounding.nearestEven_scaled_distance

/-- info: 'Acorn.weight_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.weight_legal

/-- info: 'Acorn.weight_admit_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.weight_admit_exact

/-- info: 'Acorn.weight_admit_refuses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.weight_admit_refuses

/-- info: 'Acorn.feature_index_admit_exact' does not depend on any axioms -/
#guard_msgs in
#print axioms Acorn.feature_index_admit_exact

/-- info: 'Acorn.feature_index_admit_refuses' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Acorn.feature_index_admit_refuses

/-- info: 'AcornVerif.CurrentFloat.model_mantissa_log' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_mantissa_log

/-- info: 'AcornVerif.CurrentFloat.model_normal_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_normal_target

/-- info: 'AcornVerif.CurrentFloat.model_round_fixed' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_round_fixed

/-- info: 'AcornVerif.CurrentFloat.model_scaled_mantissa' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_scaled_mantissa

/-- info: 'AcornVerif.CurrentFloat.model_round_small_nat' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_round_small_nat

/-- info: 'AcornVerif.CurrentFloat.model_unpack_pack_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_unpack_pack_normal

/-- info: 'AcornVerif.CurrentFloat.model_shift_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_shift_exact

/-- info: 'AcornVerif.CurrentFloat.model_log2_scaled' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_log2_scaled

/-- info: 'AcornVerif.CurrentFloat.model_round_scaled_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_round_scaled_exact

/-- info: 'AcornVerif.CurrentFloat.model_ofUInt64_small' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_ofUInt64_small

/-- info: 'AcornVerif.CurrentFloat.model_reencode_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_reencode_normal

/-- info: 'AcornVerif.CurrentFloat.model_mul_fraction_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_mul_fraction_scale

/-- info: 'AcornVerif.CurrentFloat.fraction_model_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.fraction_model_word

/-- info: 'AcornVerif.CurrentFloat.model_pack_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_pack_word

/-- info: 'AcornVerif.CurrentFloat.model_pack_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.model_pack_units

/-- info: 'AcornVerif.CurrentFloat.fraction_value_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.fraction_value_exact

/-- info: 'AcornVerif.CurrentFloat.fraction_word_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.fraction_word_lt_one

/-- info: 'AcornVerif.CurrentFloat.fraction_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.fraction_finite

/-- info: 'AcornVerif.CurrentFloat.nextF64_value_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.nextF64_value_exact

/-- info: 'AcornVerif.CurrentFloat.nextF64_word_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.nextF64_word_lt_one

/-- info: 'AcornVerif.CurrentPower.model_shift_mantissa' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_shift_mantissa

/-- info: 'AcornVerif.CurrentPower.model_round_mantissa_ceiling' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_round_mantissa_ceiling

/-- info: 'AcornVerif.CurrentPower.model_first_mantissa_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_first_mantissa_bound

/-- info: 'AcornVerif.CurrentPower.model_pack_below_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_pack_below_one

/-- info: 'AcornVerif.CurrentPower.model_second_shift_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_second_shift_exact

/-- info: 'AcornVerif.CurrentPower.model_round_product_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_round_product_unit

/-- info: 'AcornVerif.CurrentPower.model_log2_scaled_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_log2_scaled_positive

/-- info: 'AcornVerif.CurrentPower.model_round_scaled_normalized' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_round_scaled_normalized

/-- info: 'AcornVerif.CurrentPower.model_unpack_pack_subnormal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_unpack_pack_subnormal

/-- info: 'AcornVerif.CurrentPower.model_unpack_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_unpack_unit

/-- info: 'AcornVerif.CurrentPower.model_unit_round_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_unit_round_target

/-- info: 'AcornVerif.CurrentPower.model_unit_unpack_pack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_unit_unpack_pack

/-- info: 'AcornVerif.CurrentPower.model_unit_pack_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_unit_pack_bound

/-- info: 'AcornVerif.CurrentPower.model_ofBits_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_ofBits_unit

/-- info: 'AcornVerif.CurrentPower.model_mul_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_mul_unit

/-- info: 'AcornVerif.CurrentPower.binary64_mul_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.binary64_mul_unit

/-- info: 'AcornVerif.CurrentPower.powLoop_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.powLoop_unit

/-- info: 'Acorn.Conversion.widen_magnitude_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widen_magnitude_unit

/-- info: 'Acorn.Conversion.normalFraction_carry_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalFraction_carry_zero

/-- info: 'Acorn.Conversion.roundedNormal_zero_fraction' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.roundedNormal_zero_fraction

/-- info: 'Acorn.Conversion.normalMagnitude_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalMagnitude_unit

/-- info: 'Acorn.Conversion.narrow_magnitude_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_magnitude_unit

/-- info: 'Acorn.Conversion.widen_word_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widen_word_unit

/-- info: 'Acorn.Conversion.narrow_word_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_word_unit

/-- info: 'Acorn.Conversion.narrow_signed_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_signed_zero

/-- info: 'Acorn.Conversion.wideFields_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.wideFields_extract

/-- info: 'Acorn.Conversion.narrow_magnitude_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_magnitude_cases

/-- info: 'Acorn.Conversion.normalMagnitude_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalMagnitude_aligned

/-- info: 'Acorn.Conversion.subnormalFraction_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.subnormalFraction_aligned

/-- info: 'Acorn.Conversion.wideFields_significand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.wideFields_significand

/-- info: 'Acorn.Conversion.narrow_widen_magnitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_widen_magnitude

/-- info: 'Acorn.Conversion.narrow_widen_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_widen_finite

/-- info: 'Acorn.Conversion.narrow_widen_nonNaN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_widen_nonNaN

/-- info: 'Acorn.Conversion.widen_normal_or_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.widen_normal_or_zero

/-- info: 'Acorn.Conversion.trunc64_signed_magnitude' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.trunc64_signed_magnitude

/-- info: 'Acorn.Conversion.trunc64_signed_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.trunc64_signed_exact

/-- info: 'Acorn.Conversion.signedCast_finite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.signedCast_finite

/-- info: 'Acorn.Conversion.signedCast_finite_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.signedCast_finite_value

/-- info: 'Acorn.Rounding.wordShift_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rounding.wordShift_zero

/-- info: 'AcornVerif.CurrentFloat.ofUInt64_value_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.ofUInt64_value_exact

/-- info: 'AcornVerif.CurrentFloat.ofUInt64_word_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.ofUInt64_word_bound

/-- info: 'AcornVerif.CurrentFloat.word64_sign_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.word64_sign_exact

/-- info: 'AcornVerif.CurrentFloat.negate_magnitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.negate_magnitude

/-- info: 'AcornVerif.CurrentFloat.negate_magnitude_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.negate_magnitude_units

/-- info: 'AcornVerif.CurrentFloat.ofInt_magnitude_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.ofInt_magnitude_exact

/-- info: 'AcornVerif.CurrentFloat.ofInt_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.ofInt_finite

/-- info: 'AcornVerif.CurrentFloat.ofInt_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.ofInt_sign

/-- info: 'AcornVerif.CurrentFloat.trunc64_ofInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.trunc64_ofInt

/-- info: 'AcornVerif.CurrentFloat.toI32_ofInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentFloat.toI32_ofInt

/-- info: 'AcornVerif.CurrentPower.pow_word_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.pow_word_unit

/-- info: 'AcornVerif.CurrentPower.pow_zero_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.pow_zero_word

/-- info: 'AcornVerif.CurrentPower.mul_signed_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.mul_signed_zeros

/-- info: 'AcornVerif.CurrentPower.mul_one_signed_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.mul_one_signed_zero

/-- info: 'AcornVerif.CurrentPower.powLoop_zero_accumulator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.powLoop_zero_accumulator

/-- info: 'AcornVerif.CurrentPower.powLoop_positive_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.powLoop_positive_zero

/-- info: 'AcornVerif.CurrentPower.pow_negative_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.pow_negative_zero

/-- info: 'AcornVerif.CurrentPower.key_unit_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.key_unit_cases

/-- info: 'AcornVerif.CurrentPower.pow_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.pow_unit

/-- info: 'AcornVerif.CurrentPower.model_packComponents_unpack' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_packComponents_unpack

/-- info: 'AcornVerif.CurrentPower.model_unpack_normal_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_unpack_normal_fields

/-- info: 'AcornVerif.CurrentPower.model_pack_unpack_normal_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_pack_unpack_normal_word

/-- info: 'AcornVerif.CurrentPower.binary64_one_mul_normal_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.binary64_one_mul_normal_model

/-- info: 'AcornVerif.CurrentPower.binary64_one_mul_normal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.binary64_one_mul_normal

/-- info: 'AcornVerif.CurrentPower.model_exponent_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.model_exponent_word

/-- info: 'AcornVerif.CurrentPower.binary64_one_mul_widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.binary64_one_mul_widen

/-- info: 'AcornVerif.CurrentPower.pow_one_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPower.pow_one_word

/-- info: 'AcornVerif.CurrentExponential.powerOfTwo_word' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentExponential.powerOfTwo_word

/-- info: 'AcornVerif.CurrentExponential.powerOfTwo_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentExponential.powerOfTwo_model

/-- info: 'AcornVerif.CurrentExponential.binary64_scale_normal_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentExponential.binary64_scale_normal_model

/-- info: 'AcornVerif.CurrentExponential.model_positive_normal_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentExponential.model_positive_normal_word

/-- info: 'AcornVerif.CurrentExponential.expScale_wide_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentExponential.expScale_wide_word

/-- info: 'AcornVerif.CurrentExponential.expScale_wide_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentExponential.expScale_wide_components

/-- info: 'AcornVerif.CurrentExponential.expScale_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentExponential.expScale_nonnegative

/-- info: 'AcornVerif.CurrentExponential.expScale_negative_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentExponential.expScale_negative_unit

/-- info: 'AcornVerif.CurrentExponential.expScale_zero_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentExponential.expScale_zero_unit

/-- info: 'AcornVerif.CurrentExponential.normalExponent_no_carry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentExponential.normalExponent_no_carry

/-- info: 'AcornVerif.CurrentExponential.expScale_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentExponential.expScale_finite

/-- info: 'AcornVerif.CurrentExponential.expSaturation_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentExponential.expSaturation_ends

/-- info: 'AcornVerif.CurrentArithmetic.model_shift_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_shift_residual

/-- info: 'AcornVerif.CurrentArithmetic.model_round_shift_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_round_shift_exact

/-- info: 'AcornVerif.CurrentArithmetic.model_round_shift_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_round_shift_distance

/-- info: 'AcornVerif.CurrentArithmetic.model_first_mantissa_format' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_first_mantissa_format

/-- info: 'AcornVerif.CurrentArithmetic.model_second_shift_format' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_second_shift_format

/-- info: 'AcornVerif.CurrentArithmetic.model_round_exact_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_round_exact_components

/-- info: 'AcornVerif.CurrentArithmetic.model_round_exact_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_round_exact_value

/-- info: 'AcornVerif.CurrentArithmetic.model_round_exact_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_round_exact_error

/-- info: 'AcornVerif.CurrentArithmetic.dyadic_padding_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.dyadic_padding_exact

/-- info: 'AcornVerif.CurrentArithmetic.model_roundWithAccuracy_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_roundWithAccuracy_zero

/-- info: 'AcornVerif.CurrentArithmetic.model_round_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_round_zero

/-- info: 'AcornVerif.CurrentArithmetic.model_round_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_round_error

/-- info: 'AcornVerif.CurrentArithmetic.model_rounded_not_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_rounded_not_below

/-- info: 'AcornVerif.CurrentArithmetic.model_round_accuracy_components' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_round_accuracy_components

/-- info: 'AcornVerif.CurrentArithmetic.model_first_normalized_lower' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_first_normalized_lower

/-- info: 'AcornVerif.CurrentArithmetic.model_round_accuracy_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_round_accuracy_normalized

/-- info: 'AcornVerif.CurrentArithmetic.model_round_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_round_normalized

/-- info: 'AcornVerif.CurrentArithmetic.model_format_min_bias' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_format_min_bias

/-- info: 'AcornVerif.CurrentArithmetic.model_unpack_sign_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_unpack_sign_components

/-- info: 'AcornVerif.CurrentArithmetic.model_unpack_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_unpack_components

/-- info: 'AcornVerif.CurrentArithmetic.model_unpack_pack_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_unpack_pack_normalized

/-- info: 'AcornVerif.CurrentArithmetic.model_unpack_format' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_unpack_format

/-- info: 'AcornVerif.CurrentArithmetic.model_finite_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_finite_abs

/-- info: 'AcornVerif.CurrentArithmetic.model_fits_of_value_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_fits_of_value_bound

/-- info: 'AcornVerif.CurrentArithmetic.model_normalized_finite' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_normalized_finite

/-- info: 'AcornVerif.CurrentArithmetic.model_positive_dyadic_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_positive_dyadic_window

/-- info: 'AcornVerif.CurrentArithmetic.model_totalExponent_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_totalExponent_mono

/-- info: 'AcornVerif.CurrentArithmetic.model_normalized_target' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_normalized_target

/-- info: 'AcornVerif.CurrentArithmetic.model_round_uniform_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_round_uniform_error

/-- info: 'AcornVerif.CurrentArithmetic.model_sign_apply_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_sign_apply_value

/-- info: 'AcornVerif.CurrentArithmetic.model_sign_product_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_sign_product_value

/-- info: 'AcornVerif.CurrentArithmetic.model_signed_round_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_signed_round_value

/-- info: 'AcornVerif.CurrentArithmetic.model_format_min_nonpositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_format_min_nonpositive

/-- info: 'AcornVerif.CurrentArithmetic.model_product_exponent_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_product_exponent_ready

/-- info: 'AcornVerif.CurrentArithmetic.model_round_without_padding' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_round_without_padding

/-- info: 'AcornVerif.CurrentArithmetic.model_mul_dyadic_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_mul_dyadic_local

/-- info: 'AcornVerif.CurrentArithmetic.model_decrease_dyadic_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_decrease_dyadic_value

/-- info: 'AcornVerif.CurrentArithmetic.model_add_dyadic_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_add_dyadic_local

/-- info: 'AcornVerif.CurrentArithmetic.model_unpack_finite_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_unpack_finite_exponent

/-- info: 'AcornVerif.CurrentArithmetic.model_decoded64_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_decoded64_finite

/-- info: 'AcornVerif.CurrentArithmetic.model_decoded32_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_decoded32_finite

/-- info: 'AcornVerif.CurrentArithmetic.model_ofBits64_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_ofBits64_decoded

/-- info: 'AcornVerif.CurrentArithmetic.model_ofBits32_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_ofBits32_decoded

/-- info: 'AcornVerif.CurrentArithmetic.model_add64_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_add64_decoded

/-- info: 'AcornVerif.CurrentArithmetic.model_mul64_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_mul64_decoded

/-- info: 'AcornVerif.CurrentArithmetic.model_add32_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_add32_decoded

/-- info: 'AcornVerif.CurrentArithmetic.model_local64_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.model_local64_fits

/-- info: 'AcornVerif.CurrentArithmetic.binary64_add_finite_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.binary64_add_finite_error

/-- info: 'AcornVerif.CurrentArithmetic.binary64_mul_finite_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentArithmetic.binary64_mul_finite_error

/-- info: 'AcornVerif.CurrentOrder.fieldUnits_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.fieldUnits_zero

/-- info: 'AcornVerif.CurrentOrder.fieldUnits_strict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.fieldUnits_strict

/-- info: 'AcornVerif.CurrentOrder.fieldUnits_order' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.fieldUnits_order

/-- info: 'AcornVerif.CurrentOrder.fieldUnits_positive' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.fieldUnits_positive

/-- info: 'AcornVerif.CurrentOrder.model_finite_fields_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.model_finite_fields_value

/-- info: 'AcornVerif.CurrentOrder.fieldUnits_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.fieldUnits_fields

/-- info: 'AcornVerif.CurrentOrder.model_finite_fieldUnits_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.model_finite_fieldUnits_value

/-- info: 'AcornVerif.CurrentOrder.numerical64_fieldUnits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical64_fieldUnits

/-- info: 'AcornVerif.CurrentOrder.numerical32_fieldUnits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical32_fieldUnits

/-- info: 'AcornVerif.CurrentOrder.signedFieldUnits_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.signedFieldUnits_sign

/-- info: 'AcornVerif.CurrentOrder.signedFieldUnits_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.signedFieldUnits_strict

/-- info: 'AcornVerif.CurrentOrder.signedFieldUnits_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.signedFieldUnits_order

/-- info: 'AcornVerif.CurrentOrder.model_word64_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.model_word64_sign

/-- info: 'AcornVerif.CurrentOrder.numerical64_key_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical64_key_units

/-- info: 'AcornVerif.CurrentOrder.numerical64_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical64_order

/-- info: 'AcornVerif.CurrentOrder.word32_sign_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.word32_sign_exact

/-- info: 'AcornVerif.CurrentOrder.model_word32_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.model_word32_sign

/-- info: 'AcornVerif.CurrentOrder.numerical32_key_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical32_key_units

/-- info: 'AcornVerif.CurrentOrder.numerical32_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical32_order

/-- info: 'AcornVerif.CurrentOrder.numerical64_strict_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical64_strict_order

/-- info: 'AcornVerif.CurrentOrder.numerical32_strict_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical32_strict_order

/-- info: 'AcornVerif.CurrentOrder.numerical64_less' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical64_less

/-- info: 'AcornVerif.CurrentOrder.numerical32_less' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical32_less

/-- info: 'AcornVerif.CurrentOrder.magnitudeUnits32_fieldUnits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.magnitudeUnits32_fieldUnits

/-- info: 'AcornVerif.CurrentOrder.numerical64_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical64_units

/-- info: 'AcornVerif.CurrentOrder.numerical32_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical32_units

/-- info: 'AcornVerif.CurrentOrder.numerical_widen_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical_widen_exact

/-- info: 'AcornVerif.CurrentOrder.sign_dyadic_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.sign_dyadic_abs

/-- info: 'AcornVerif.CurrentOrder.numerical64_abs_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical64_abs_units

/-- info: 'AcornVerif.CurrentOrder.numerical32_abs_units' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical32_abs_units

/-- info: 'AcornVerif.CurrentOrder.numerical64_magnitude_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical64_magnitude_order

/-- info: 'AcornVerif.CurrentOrder.numerical32_magnitude_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical32_magnitude_order

/-- info: 'AcornVerif.CurrentOrder.numerical64_ofInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical64_ofInt

/-- info: 'AcornVerif.CurrentOrder.numerical64_ofUInt64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOrder.numerical64_ofUInt64

/-- info: 'AcornVerif.CurrentOperations.model_sign_neg_apply' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOperations.model_sign_neg_apply

/-- info: 'AcornVerif.CurrentOperations.model_sub_add_neg' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOperations.model_sub_add_neg

/-- info: 'AcornVerif.CurrentOperations.model_neg_normalized' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOperations.model_neg_normalized

/-- info: 'AcornVerif.CurrentOperations.model_neg_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOperations.model_neg_value

/-- info: 'AcornVerif.CurrentOperations.model_sub_dyadic_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOperations.model_sub_dyadic_local

/-- info: 'AcornVerif.CurrentOperations.model_sub64_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOperations.model_sub64_decoded

/-- info: 'AcornVerif.CurrentOperations.binary64_sub_finite_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOperations.binary64_sub_finite_error

/-- info: 'AcornVerif.CurrentOperations.quotient_fraction_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOperations.quotient_fraction_bracket

/-- info: 'AcornVerif.CurrentOperations.numerical64_trunc_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOperations.numerical64_trunc_signed

/-- info: 'AcornVerif.CurrentOperations.numerical64_trunc_toward_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOperations.numerical64_trunc_toward_zero

/-- info: 'AcornVerif.CurrentOperations.numerical64_trunc_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOperations.numerical64_trunc_abs

/-- info: 'AcornVerif.CurrentOperations.numerical64_toI32_trunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentOperations.numerical64_toI32_trunc

/-- info: 'AcornVerif.CurrentDivision.model_round_accuracy_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentDivision.model_round_accuracy_value

/-- info: 'AcornVerif.CurrentDivision.model_round_accuracy_distance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentDivision.model_round_accuracy_distance

/-- info: 'AcornVerif.CurrentDivision.model_ratio_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentDivision.model_ratio_positive

/-- info: 'AcornVerif.CurrentDivision.model_ratio_window_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentDivision.model_ratio_window_lower

/-- info: 'AcornVerif.CurrentDivision.model_divCore_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentDivision.model_divCore_bracket

/-- info: 'AcornVerif.CurrentDivision.model_round_accuracy_zero_normalized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentDivision.model_round_accuracy_zero_normalized

/-- info: 'AcornVerif.CurrentDivision.model_divCore_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentDivision.model_divCore_ready

/-- info: 'AcornVerif.CurrentDivision.model_divCore_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentDivision.model_divCore_error

/-- info: 'AcornVerif.CurrentDivision.model_signed_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentDivision.model_signed_ratio

/-- info: 'AcornVerif.CurrentDivision.model_div_dyadic_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentDivision.model_div_dyadic_local

/-- info: 'AcornVerif.CurrentDivision.model_div64_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentDivision.model_div64_decoded

/-- info: 'AcornVerif.CurrentDivision.binary64_div_finite_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentDivision.binary64_div_finite_error

/-- info: 'AcornVerif.CurrentIntervals.model_sub_positive_zero' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.CurrentIntervals.model_sub_positive_zero

/-- info: 'AcornVerif.CurrentIntervals.binary64_sub_zero_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentIntervals.binary64_sub_zero_value

/-- info: 'AcornVerif.CurrentIntervals.model_mul_nonpositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentIntervals.model_mul_nonpositive

/-- info: 'AcornVerif.CurrentIntervals.binary64_mul_nonpositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentIntervals.binary64_mul_nonpositive

/-- info: 'AcornVerif.CurrentIntervals.numerical64_above_one_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentIntervals.numerical64_above_one_gap

/-- info: 'AcornVerif.CurrentIntervals.binary64_add_unit_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentIntervals.binary64_add_unit_upper

/-- info: 'AcornVerif.CurrentIntervals.binary64_key_nonnegative_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentIntervals.binary64_key_nonnegative_word

/-- info: 'AcornVerif.CurrentIntervals.binary64_positive_key_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentIntervals.binary64_positive_key_word

/-- info: 'AcornVerif.CurrentIntervals.narrow_finite_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentIntervals.narrow_finite_local

/-- info: 'AcornVerif.CurrentReduction.reduction_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentReduction.reduction_constants

/-- info: 'AcornVerif.CurrentReduction.trunc_selection_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentReduction.trunc_selection_band

/-- info: 'AcornVerif.CurrentReduction.expReduce_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentReduction.expReduce_contract

/-- info: 'AcornVerif.CurrentReduction.expReduce_zero_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentReduction.expReduce_zero_remainder

/-- info: 'AcornVerif.CurrentReduction.exp_admitted_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentReduction.exp_admitted_reduction

/-- info: 'AcornVerif.CurrentSeries.hornerStep_finite_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentSeries.hornerStep_finite_error

/-- info: 'AcornVerif.CurrentSeries.hornerFrom_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentSeries.hornerFrom_envelope

/-- info: 'AcornVerif.CurrentSeries.reciprocal_coefficient_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentSeries.reciprocal_coefficient_bound

/-- info: 'AcornVerif.CurrentSeries.expSeries_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentSeries.expSeries_contract

/-- info: 'AcornVerif.CurrentPortable.exp_polynomial_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPortable.exp_polynomial_words

/-- info: 'AcornVerif.CurrentPortable.exp_admitted_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPortable.exp_admitted_contract

/-- info: 'AcornVerif.CurrentPortable.exp_nonNaN_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPortable.exp_nonNaN_word

/-- info: 'AcornVerif.CurrentPortable.exp_nonpositive_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPortable.exp_nonpositive_unit

/-- info: 'AcornVerif.CurrentLogarithm.approximation_magnitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLogarithm.approximation_magnitude

/-- info: 'AcornVerif.CurrentLogarithm.ln_mantissa_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLogarithm.ln_mantissa_fields

/-- info: 'AcornVerif.CurrentLogarithm.ln_body_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLogarithm.ln_body_finite

/-- info: 'AcornVerif.CurrentLogarithm.ln_total_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLogarithm.ln_total_contract


/-- info: 'AcornVerif.CurrentPrediction.model_round_uniform_error_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPrediction.model_round_uniform_error_strict

/-- info: 'AcornVerif.CurrentPrediction.model_signed_round_value_strict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPrediction.model_signed_round_value_strict

/-- info: 'AcornVerif.CurrentPrediction.model_add_dyadic_local_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPrediction.model_add_dyadic_local_strict

/-- info: 'AcornVerif.CurrentPrediction.binary32_add_finite_strict_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPrediction.binary32_add_finite_strict_error

/-- info: 'AcornVerif.CurrentPrediction.weight_numerical_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPrediction.weight_numerical_bound

/-- info: 'AcornVerif.CurrentPrediction.numerical32_prediction_cap_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPrediction.numerical32_prediction_cap_gap

/-- info: 'AcornVerif.CurrentPrediction.prediction_sum_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPrediction.prediction_sum_cap

/-- info: 'AcornVerif.CurrentPrediction.prediction_sum_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPrediction.prediction_sum_step

/-- info: 'AcornVerif.CurrentPrediction.prediction_sumFrom_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPrediction.prediction_sumFrom_bound

/-- info: 'AcornVerif.CurrentPrediction.legal_weight_sum_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentPrediction.legal_weight_sum_bound


/-- info: 'AcornVerif.CurrentState.discount_numeric_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentState.discount_numeric_contract

/-- info: 'AcornVerif.CurrentState.config_log_rail_nonpositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentState.config_log_rail_nonpositive

/-- info: 'AcornVerif.CurrentState.log_step_alpha_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentState.log_step_alpha_unit


/-- info: 'Acorn.Rounding.nearestEven_word_large_shift' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Rounding.nearestEven_word_large_shift

/-- info: 'Acorn.Conversion.normalMagnitude_components' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.normalMagnitude_components

/-- info: 'AcornVerif.CurrentLearnerArithmetic.mul32_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.mul32_decoded

/-- info: 'AcornVerif.CurrentLearnerArithmetic.div32_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.div32_decoded

/-- info: 'AcornVerif.CurrentLearnerArithmetic.local32_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.local32_fits

/-- info: 'AcornVerif.CurrentLearnerArithmetic.round_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.round_nonnegative

/-- info: 'AcornVerif.CurrentLearnerArithmetic.finite_nonnegative_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.finite_nonnegative_sign

/-- info: 'AcornVerif.CurrentLearnerArithmetic.model_mul_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.model_mul_nonnegative

/-- info: 'AcornVerif.CurrentLearnerArithmetic.model_div_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.model_div_nonnegative

/-- info: 'AcornVerif.CurrentLearnerArithmetic.mul32_nonnegative_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.mul32_nonnegative_bound

/-- info: 'AcornVerif.CurrentLearnerArithmetic.div32_nonnegative_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.div32_nonnegative_bound

/-- info: 'AcornVerif.CurrentLearnerArithmetic.word_unit_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.word_unit_interval

/-- info: 'AcornVerif.CurrentLearnerArithmetic.alpha_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.alpha_numeric

/-- info: 'AcornVerif.CurrentLearnerArithmetic.alpha_sum_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.alpha_sum_finite

/-- info: 'AcornVerif.CurrentLearnerArithmetic.eta_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.eta_numeric

/-- info: 'AcornVerif.CurrentLearnerArithmetic.word_half_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.word_half_interval

/-- info: 'AcornVerif.CurrentLearnerArithmetic.epsilon_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.epsilon_numeric

/-- info: 'AcornVerif.CurrentLearnerArithmetic.denominator_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.denominator_numeric

/-- info: 'AcornVerif.CurrentLearnerArithmetic.trace_increment_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.trace_increment_numeric

/-- info: 'AcornVerif.CurrentLearnerArithmetic.pruning_threshold_numeric' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearnerArithmetic.pruning_threshold_numeric

/-- info: 'AcornVerif.CurrentLearner.vector_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.vector_get

/-- info: 'AcornVerif.CurrentLearner.finite_equal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.finite_equal

/-- info: 'AcornVerif.CurrentLearner.finite_lessOrEqual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.finite_lessOrEqual

/-- info: 'AcornVerif.CurrentLearner.zero_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.zero_key

/-- info: 'AcornVerif.CurrentLearner.zero_pruned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.zero_pruned

/-- info: 'AcornVerif.CurrentLearner.active_cardinality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.active_cardinality

/-- info: 'AcornVerif.CurrentLearner.eligible_cardinality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.eligible_cardinality

/-- info: 'AcornVerif.CurrentLearner.knowledge_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.knowledge_legal

/-- info: 'AcornVerif.CurrentLearner.prediction_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.prediction_bound

/-- info: 'AcornVerif.CurrentLearner.clear_transient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.clear_transient

/-- info: 'AcornVerif.CurrentLearner.clear_knowledge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.clear_knowledge

/-- info: 'AcornVerif.CurrentLearner.initial_transient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.initial_transient

/-- info: 'AcornVerif.CurrentLearner.step_observation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.step_observation

/-- info: 'AcornVerif.CurrentLearner.terminal_transient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.terminal_transient

/-- info: 'AcornVerif.CurrentLearner.install_transient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.install_transient

/-- info: 'AcornVerif.CurrentLearner.swap_remove_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.swap_remove_size

/-- info: 'AcornVerif.CurrentLearner.array_nodup_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.array_nodup_iff

/-- info: 'AcornVerif.CurrentLearner.swap_remove_get' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.swap_remove_get

/-- info: 'AcornVerif.CurrentLearner.swap_remove_subset' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.swap_remove_subset

/-- info: 'AcornVerif.CurrentLearner.swap_remove_preserves_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.swap_remove_preserves_other

/-- info: 'AcornVerif.CurrentLearner.swap_remove_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.swap_remove_nodup

/-- info: 'AcornVerif.CurrentLearner.restore_prefix_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.restore_prefix_get

/-- info: 'AcornVerif.CurrentLearner.restore_weights_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.restore_weights_get

/-- info: 'AcornVerif.CurrentLearner.restore_beta_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.restore_beta_get

/-- info: 'AcornVerif.CurrentLearner.clear_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.clear_core

/-- info: 'AcornVerif.CurrentLearner.clear_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.clear_ready

/-- info: 'AcornVerif.CurrentLearner.initial_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.initial_core

/-- info: 'AcornVerif.CurrentLearner.initial_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.initial_ready

/-- info: 'AcornVerif.CurrentLearner.clear_feature_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.clear_feature_self

/-- info: 'AcornVerif.CurrentLearner.clear_feature_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.clear_feature_other

/-- info: 'AcornVerif.CurrentLearner.first_element_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_element_frame

/-- info: 'AcornVerif.CurrentLearner.first_element_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_element_reference

/-- info: 'AcornVerif.CurrentLearner.first_element_eligible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_element_eligible

/-- info: 'AcornVerif.CurrentLearner.first_element_prune' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_element_prune

/-- info: 'AcornVerif.CurrentLearner.second_element_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_element_frame

/-- info: 'AcornVerif.CurrentLearner.second_element_eligible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_element_eligible

/-- info: 'AcornVerif.CurrentLearner.registers_zero_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.registers_zero_trace

/-- info: 'AcornVerif.CurrentLearner.registers_trace_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.registers_trace_eq

/-- info: 'AcornVerif.CurrentLearner.registers_reference_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.registers_reference_eq

/-- info: 'AcornVerif.CurrentLearner.clear_feature_references' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.clear_feature_references

/-- info: 'AcornVerif.CurrentLearner.first_element_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_element_supported

/-- info: 'AcornVerif.CurrentLearner.prune_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.prune_supported

/-- info: 'AcornVerif.CurrentLearner.first_loop_go_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_loop_go_core

/-- info: 'AcornVerif.CurrentLearner.first_loop_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_loop_core

/-- info: 'AcornVerif.CurrentLearner.second_element_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_element_reference

/-- info: 'AcornVerif.CurrentLearner.second_element_contains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_element_contains

/-- info: 'AcornVerif.CurrentLearner.second_element_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_element_self

/-- info: 'AcornVerif.CurrentLearner.second_element_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_element_supported

/-- info: 'AcornVerif.CurrentLearner.second_element_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_element_core

/-- info: 'AcornVerif.CurrentLearner.second_fold_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_fold_core

/-- info: 'AcornVerif.CurrentLearner.second_loop_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_loop_core

/-- info: 'AcornVerif.CurrentLearner.second_fold_eligible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_fold_eligible

/-- info: 'AcornVerif.CurrentLearner.second_loop_eligible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_loop_eligible

/-- info: 'AcornVerif.CurrentLearner.second_loop_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_loop_count

/-- info: 'AcornVerif.CurrentLearner.second_loop_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_loop_count_le

/-- info: 'AcornVerif.CurrentLearner.second_loop_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_loop_unique

/-- info: 'AcornVerif.CurrentLearner.first_element_retained_nonzero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_element_retained_nonzero

/-- info: 'AcornVerif.CurrentLearner.first_element_processed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_element_processed

/-- info: 'AcornVerif.CurrentLearner.prune_processed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.prune_processed

/-- info: 'AcornVerif.CurrentLearner.first_loop_go_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_loop_go_ready

/-- info: 'AcornVerif.CurrentLearner.first_loop_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_loop_ready

/-- info: 'AcornVerif.CurrentLearner.core_of_transient_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.core_of_transient_eq

/-- info: 'AcornVerif.CurrentLearner.ready_of_transient_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.ready_of_transient_eq

/-- info: 'AcornVerif.CurrentLearner.plan_fold_transient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.plan_fold_transient

/-- info: 'AcornVerif.CurrentLearner.plan_transient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.plan_transient

/-- info: 'AcornVerif.CurrentLearner.step_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.step_core

/-- info: 'AcornVerif.CurrentLearner.begin_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.begin_core

/-- info: 'AcornVerif.CurrentLearner.terminal_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.terminal_core

/-- info: 'AcornVerif.CurrentLearner.install_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.install_core

/-- info: 'AcornVerif.CurrentLearner.clear_feature_supported' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.clear_feature_supported

/-- info: 'AcornVerif.CurrentLearner.retire_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.retire_core

/-- info: 'AcornVerif.CurrentLearner.entry_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.entry_core

/-- info: 'AcornVerif.CurrentLearner.entries_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.entries_core

/-- info: 'AcornVerif.CurrentLearner.admitted_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.admitted_core

/-- info: 'AcornVerif.CurrentLearner.learner_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.learner_invariant

/-- info: 'AcornVerif.CurrentLearner.swap_remove_absent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.swap_remove_absent

/-- info: 'AcornVerif.CurrentLearner.retire_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.retire_unique

/-- info: 'AcornVerif.CurrentLearner.retire_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.retire_ready

/-- info: 'AcornVerif.CurrentLearner.entry_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.entry_schedule

/-- info: 'AcornVerif.CurrentLearner.entries_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.entries_schedule

/-- info: 'AcornVerif.CurrentLearner.scheduled_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.scheduled_capacity

/-- info: 'AcornVerif.CurrentLearner.prune_work_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.prune_work_decreases

/-- info: 'AcornVerif.CurrentLearner.retain_work_decreases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.retain_work_decreases

/-- info: 'AcornVerif.CurrentLearner.first_loop_go_size' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_loop_go_size

/-- info: 'AcornVerif.CurrentLearner.retained_slots_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.retained_slots_exact

/-- info: 'AcornVerif.CurrentLearner.retained_slots_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.retained_slots_unique

/-- info: 'AcornVerif.CurrentLearner.scheduled_storage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.scheduled_storage

/-- info: 'AcornVerif.CurrentLearner.retire_registers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.retire_registers

/-- info: 'AcornVerif.CurrentLearner.normalized_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.normalized_count

/-- info: 'AcornVerif.CurrentLearner.clear_observers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.clear_observers

/-- info: 'AcornVerif.CurrentLearner.exploration_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.exploration_legal

/-- info: 'AcornVerif.CurrentLearner.consumer_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.consumer_own

/-- info: 'AcornVerif.CurrentLearner.every_consumer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.every_consumer

/-- info: 'AcornVerif.CurrentLearner.first_element_reanchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.first_element_reanchor

/-- info: 'AcornVerif.CurrentLearner.second_element_overshoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLearner.second_element_overshoot

/-- info: 'Acorn.Features.Skill.step_age' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Features.Skill.step_age

/-- info: 'Acorn.Features.Skill.step_frozen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Features.Skill.step_frozen

/-- info: 'AcornVerif.CurrentTemporal.stored_mode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentTemporal.stored_mode

/-- info: 'AcornVerif.CurrentTemporal.served_preempts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentTemporal.served_preempts

/-- info: 'AcornVerif.CurrentTemporal.service_prefix_exact' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentTemporal.service_prefix_exact

/-- info: 'AcornVerif.TemporalSupport.action_composition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.TemporalSupport.action_composition

/-- info: 'AcornVerif.TemporalSupport.served_other_mass_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.TemporalSupport.served_other_mass_zero


/-- info: 'AcornVerif.CurrentAgent.initialization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentAgent.initialization

/-- info: 'AcornVerif.CurrentAgent.native_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentAgent.native_prefix

/-- info: 'AcornVerif.CurrentLifetime.stored_sum_legal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentLifetime.stored_sum_legal

/-- info: 'Acorn.Handcrafted.TemporalControl.step_episodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Handcrafted.TemporalControl.step_episodes

/-- info: 'Acorn.Handcrafted.TemporalControl.step_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Handcrafted.TemporalControl.step_total

/-- info: 'Acorn.Checkpoint.roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Checkpoint.roundtrip

/-- info: 'Acorn.Checkpoint.load_nonmutation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Checkpoint.load_nonmutation

/-- info: 'Acorn.Checkpoint.snapshot_size_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Checkpoint.snapshot_size_bound

/-- info: 'Acorn.Handcrafted.Agent.restore_components' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Handcrafted.Agent.restore_components

/-- info: 'AcornVerif.CurrentCheckpoint.saved_weight_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentCheckpoint.saved_weight_identity

/-- info: 'AcornVerif.CurrentCheckpoint.saved_beta_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentCheckpoint.saved_beta_identity

/-- info: 'AcornVerif.CurrentCheckpoint.candidate_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentCheckpoint.candidate_roundtrip

/-- info: 'AcornVerif.CurrentCheckpoint.save_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentCheckpoint.save_load

/-- info: 'AcornVerif.CurrentConstants.discount_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentConstants.discount_values

/-- info: 'AcornVerif.CurrentConstants.numeric_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentConstants.numeric_values

/-- info: 'AcornVerif.CurrentConstants.dimensions' does not depend on any axioms -/
#guard_msgs in
#print axioms AcornVerif.CurrentConstants.dimensions

/-- info: 'AcornVerif.CurrentConstants.study_inputs' does not depend on any axioms -/
#guard_msgs in
#print axioms AcornVerif.CurrentConstants.study_inputs

/-- info: 'AcornVerif.CurrentRetirement.zero_add_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.zero_add_numeric

/-- info: 'AcornVerif.CurrentRetirement.sub_zero_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.sub_zero_numeric

/-- info: 'AcornVerif.CurrentRetirement.abs_word_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.abs_word_eq

/-- info: 'AcornVerif.CurrentRetirement.retirement_disruption_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.retirement_disruption_bounded

/-- info: 'AcornVerif.CurrentRetirement.rail_floor_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.rail_floor_word

/-- info: 'AcornVerif.CurrentRetirement.rail_floor_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.rail_floor_decoded

/-- info: 'AcornVerif.CurrentRetirement.floor_add_unpacked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.floor_add_unpacked

/-- info: 'AcornVerif.CurrentRetirement.packed_floor_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.packed_floor_key

/-- info: 'AcornVerif.CurrentRetirement.floor_add_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.floor_add_key

/-- info: 'AcornVerif.CurrentRetirement.saturation_floor_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.saturation_floor_key

/-- info: 'AcornVerif.CurrentRetirement.downward_projection_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.downward_projection_floor

/-- info: 'AcornVerif.CurrentRetirement.floor_key_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.floor_key_unique

/-- info: 'AcornVerif.CurrentRetirement.downward_projection_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.downward_projection_word

/-- info: 'AcornVerif.CurrentRetirement.zero_below_disruption' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.zero_below_disruption

/-- info: 'AcornVerif.CurrentRetirement.retirement_predicate_reachable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirement.retirement_predicate_reachable

/-- info: 'AcornVerif.CurrentRetirementRounding.nearest_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirementRounding.nearest_lower

/-- info: 'AcornVerif.CurrentRetirementRounding.rounded_grid_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirementRounding.rounded_grid_lower

/-- info: 'AcornVerif.CurrentRetirementRounding.dyadic_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirementRounding.dyadic_lower

/-- info: 'AcornVerif.CurrentRetirementRounding.round_grid_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirementRounding.round_grid_bound

/-- info: 'AcornVerif.CurrentRetirementRounding.round_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirementRounding.round_lower

/-- info: 'AcornVerif.CurrentRetirementRounding.round_negative_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirementRounding.round_negative_value

/-- info: 'AcornVerif.CurrentRetirementRounding.normalize_negative_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentRetirementRounding.normalize_negative_bound

/-- info: 'AcornVerif.CurrentTemporal.terminal_coordinate_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentTemporal.terminal_coordinate_exact


/-- info: 'AcornVerif.CurrentBackupBounds.nearest_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.nearest_upper

/-- info: 'AcornVerif.CurrentBackupBounds.dyadic_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.dyadic_upper

/-- info: 'AcornVerif.CurrentBackupBounds.round_grid_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.round_grid_upper

/-- info: 'AcornVerif.CurrentBackupBounds.round_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.round_upper

/-- info: 'AcornVerif.CurrentBackupBounds.round_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.round_nonnegative

/-- info: 'AcornVerif.CurrentBackupBounds.nearest_fraction_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.nearest_fraction_mono

/-- info: 'AcornVerif.CurrentBackupBounds.round_grid_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.round_grid_representation

/-- info: 'AcornVerif.CurrentBackupBounds.round_positive_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.round_positive_mono

/-- info: 'AcornVerif.CurrentBackupBounds.normalize_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.normalize_zero

/-- info: 'AcornVerif.CurrentBackupBounds.normalize_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.normalize_positive

/-- info: 'AcornVerif.CurrentBackupBounds.normalize_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.normalize_negative

/-- info: 'AcornVerif.CurrentBackupBounds.normalize_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.normalize_nonnegative

/-- info: 'AcornVerif.CurrentBackupBounds.normalize_nonpositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.normalize_nonpositive

/-- info: 'AcornVerif.CurrentBackupBounds.normalize_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.normalize_mono

/-- info: 'AcornVerif.CurrentBackupBounds.normalize_sign_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.normalize_sign_value

/-- info: 'AcornVerif.CurrentBackupBounds.round_normalized_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.round_normalized_value

/-- info: 'AcornVerif.CurrentBackupBounds.Rounded.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.Rounded.mono

/-- info: 'AcornVerif.CurrentBackupBounds.rounded_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.rounded_normalized

/-- info: 'AcornVerif.CurrentBackupBounds.rounded_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.rounded_add

/-- info: 'AcornVerif.CurrentBackupBounds.rounded_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.rounded_mul

/-- info: 'AcornVerif.CurrentBackupBounds.normalize_neg_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.normalize_neg_value

/-- info: 'AcornVerif.CurrentBackupBounds.Rounded.neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.Rounded.neg

/-- info: 'AcornVerif.CurrentBackupBounds.binary32_rounded_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.binary32_rounded_exact

/-- info: 'AcornVerif.CurrentBackupBounds.binary32_rounded_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.binary32_rounded_add

/-- info: 'AcornVerif.CurrentBackupBounds.binary32_rounded_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.binary32_rounded_mul

/-- info: 'AcornVerif.CurrentBackupBounds.binary32_rounded_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.binary32_rounded_sub

/-- info: 'AcornVerif.CurrentBackupBounds.centered_reward_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.centered_reward_bound

/-- info: 'AcornVerif.CurrentBackupBounds.differential_backup_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.differential_backup_bound

/-- info: 'AcornVerif.CurrentBackupBounds.model_prediction_differential_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.model_prediction_differential_bound

/-- info: 'AcornVerif.CurrentBackupBounds.rounded_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.rounded_zero

/-- info: 'AcornVerif.CurrentBackupBounds.discounted_product_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.discounted_product_interval

/-- info: 'AcornVerif.CurrentBackupBounds.prediction_difference_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.prediction_difference_interval

/-- info: 'AcornVerif.CurrentBackupBounds.discount_arithmetic_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.discount_arithmetic_domain

/-- info: 'AcornVerif.CurrentBackupBounds.reward_sum_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.reward_sum_interval

/-- info: 'AcornVerif.CurrentBackupBounds.prediction_numeric_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.prediction_numeric_bounds

/-- info: 'AcornVerif.CurrentBackupBounds.option_td_error_termination_conditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.CurrentBackupBounds.option_td_error_termination_conditional

/-- info: 'Acorn.Binary64.less_eq_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Binary64.less_eq_key

/-- info: 'Acorn.Conversion.toI32_eq_signedCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.toI32_eq_signedCast

/-- info: 'Acorn.Portable.powerOfTwoWord_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Portable.powerOfTwoWord_eq

/-- info: 'Acorn.Portable.exp_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Portable.exp_eq_spec

/-- info: 'AcornVerif.Resource.WordTree.exec_le_bound' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.Resource.WordTree.exec_le_bound

/-- info: 'AcornVerif.Resource.BudgetedTree.exec_le_limit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.Resource.BudgetedTree.exec_le_limit

/-- info: 'Acorn.Conversion.narrow_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.narrow_def

/-- info: 'Acorn.Conversion.toI64_eq_signedCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Conversion.toI64_eq_signedCast

/-- info: 'Acorn.Host.floor32_eq_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Acorn.Host.floor32_eq_spec

/-- info: 'AcornVerif.Resource.WordTree.costExec_le_cost' depends on axioms: [propext] -/
#guard_msgs in
#print axioms AcornVerif.Resource.WordTree.costExec_le_cost

/-- info: 'AcornVerif.Resource.InitExec.credit_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.Resource.InitExec.credit_bound

/-- info: 'AcornVerif.Resource.HalvingExec.cost_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AcornVerif.Resource.HalvingExec.cost_bound

end AcornVerif
