/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Host.AgentInterface
import Acorn.Host.Viewer.TelemetryValue

/-!
# Lifetime telemetry projections

Every sum, count, return and error is read from the actual lifetime owner.
Channel-indexed records are traversed in their storage order; cycle aggregates
are family-major. No observer accumulator is substituted for the agent's
checkpoint-persistent experience record.
-/
namespace Acorn.Host.Viewer
open Features Handcrafted Lifetime

/-- Read one same-typed projection from every horizon-indexed durable record. -/
def demonLifetimeValues {α : Type} {discounts : List Discount}
    (read : (discount : Discount) → DemonDurable discount → α)
    (records : DemonRecords discounts) : Vector α discounts.length :=
  match records with
  | .nil => #v[]
  | .cons head tail => (#v[read _ head.durable] ++ demonLifetimeValues read tail).cast (by simp [Nat.add_comm])

/-- Read authoritative process-local channels in their exact typed inventory order. -/
def demonProcessValues {α : Type} {discounts : List Discount}
    (read : (discount : Discount) → DemonStats discount → α)
    (records : DemonRecords discounts) : Vector α discounts.length :=
  match records with
  | .nil => #v[]
  | .cons head tail => (#v[read _ head] ++ demonProcessValues read tail).cast (by simp [Nat.add_comm])

private def agreementStatus {discount : Discount} (state : DemonStats discount) : String :=
  match state.agreement.fault with
  | some .invalid => "invalid"
  | some .saturated => "saturated"
  | none =>
    if state.agreement.censored.val > 0 then
      if state.agreement.total.count.val > 0 then "partially censored" else "censored"
    else if state.pendingCount > 0 then "pending"
    else if state.agreement.total.count.val > 0 then "complete" else "empty"

/-- Process-session score and coverage are projected from the core, never accumulated by a browser. -/
def agreementTelemetry {config : Features.Config} {dimension : Dimension}
    (agent : AgentObservation config dimension) : List TelemetryField :=
  let life := agent.lifetime
  let score := life.demons.agreementRatio
  [⟨"agreement_version", .natural, 1⟩,
   ⟨"agreement_scale", .natural, Agreement.displayScale⟩,
   ⟨"agreement_started", .optional .natural, life.agreementStarted.map UInt64.toNat⟩,
   ⟨"agreement_stopped", .flag, life.agreementStopped⟩,
   ⟨"agreement_score", .optional .natural, score.map Agreement.Ratio.agreementUnits⟩,
   ⟨"agreement_text", .optional .text, score.map Agreement.Ratio.agreementText⟩,
   ⟨"agreement_error", .optional .natural, score.map Agreement.Ratio.errorUnits⟩,
   ⟨"agreement_channel_score", .array demonLayout.length (.optional .natural),
     demonProcessValues (fun _ state => state.agreement.ratio.map Agreement.Ratio.agreementUnits) life.demons⟩,
   ⟨"agreement_channel_text", .array demonLayout.length (.optional .text),
     demonProcessValues (fun _ state => state.agreement.ratio.map Agreement.Ratio.agreementText) life.demons⟩,
   ⟨"agreement_channel_error", .array demonLayout.length (.optional .natural),
     demonProcessValues (fun _ state => state.agreement.ratio.map Agreement.Ratio.errorUnits) life.demons⟩,
   ⟨"agreement_count", .array demonLayout.length .text,
     demonProcessValues (fun _ state => toString state.agreement.total.count.val) life.demons⟩,
   ⟨"agreement_pending", .array demonLayout.length .natural,
     demonProcessValues (fun _ state => state.pendingCount) life.demons⟩,
   ⟨"agreement_censored", .array demonLayout.length .text,
     demonProcessValues (fun _ state => toString state.agreement.censored.val) life.demons⟩,
   ⟨"agreement_status", .array demonLayout.length .text,
     demonProcessValues (fun _ state => agreementStatus state) life.demons⟩,
   ⟨"agreement_horizon", .array demonLayout.length .natural,
     demonProcessValues (fun _ state => state.settleAfter.val.val) life.demons⟩,
   ⟨"agreement_start_first", .array demonLayout.length (.optional .natural),
     demonProcessValues (fun _ state => state.agreement.starts.map (·.first.toNat)) life.demons⟩,
   ⟨"agreement_start_last", .array demonLayout.length (.optional .natural),
     demonProcessValues (fun _ state => state.agreement.starts.map (·.last.toNat)) life.demons⟩,
   ⟨"agreement_settlement_first", .array demonLayout.length (.optional .natural),
     demonProcessValues (fun _ state => state.agreement.settlements.map (·.first.toNat)) life.demons⟩,
   ⟨"agreement_settlement_last", .array demonLayout.length (.optional .natural),
     demonProcessValues (fun _ state => state.agreement.settlements.map (·.last.toNat)) life.demons⟩,
   ⟨"agreement_tail", .array demonLayout.length (.optional .natural),
     demonProcessValues (fun _ state => state.agreement.precision.map (·.tail.upperUnits)) life.demons⟩,
   ⟨"agreement_rounding", .array demonLayout.length (.optional .natural),
     demonProcessValues (fun _ state => state.agreement.precision.map (·.rounding.upperUnits)) life.demons⟩,
   ⟨"agreement_history_clock", .array Acorn.FeatureConstants.historyBins (.optional .natural),
     life.agreementHistory.map (fun point => point.map (·.clock.toNat))⟩,
   ⟨"agreement_history_score", .array Acorn.FeatureConstants.historyBins (.optional .natural),
     life.agreementHistory.map (fun point => point.map (·.ratio.agreementUnits))⟩]

private def wordArray {α : Type} {count : Nat} (name : String)
    (values : Vector α count) (read : α → UInt64) : TelemetryField :=
  ⟨name, .array count .natural, values.map (fun value => (read value).toNat)⟩

private def sumArray {quantity : Quantity} {count : Nat} (name : String)
    (values : Vector (SumCount quantity) count) : TelemetryField :=
  ⟨name, .array count .binary64, values.map (·.sum)⟩

/-- Emit all lifetime totals and settlement diagnostics, preserving their exact stored shapes. -/
def lifetimeTelemetry {config : Features.Config} {dimension : Dimension}
    (agent : AgentObservation config dimension) : List TelemetryField :=
  let life := agent.lifetime
  [⟨"lifetime_reward_sum", .binary64, life.reward.sum⟩,
   ⟨"lifetime_reward_count", .natural, life.reward.count.toNat⟩,
   sumArray "lifetime_reward_family_sum" life.rewardByFamily,
   wordArray "lifetime_reward_family_count" life.rewardByFamily (·.count),
   sumArray "lifetime_reward_history_sum" life.rewardHistory,
   wordArray "lifetime_reward_history_count" life.rewardHistory (·.count),
   sumArray "lifetime_error_history_sum" life.errorHistory,
   wordArray "lifetime_error_history_count" life.errorHistory (·.count),
   ⟨"lifetime_error_sum", .array demonLayout.length .binary64,
      demonLifetimeValues (fun _ state => state.squaredError.sum) life.demons⟩,
   ⟨"lifetime_error_count", .array demonLayout.length .natural,
      demonLifetimeValues (fun _ state => state.squaredError.count.toNat) life.demons⟩,
   ⟨"settled_return", .array demonLayout.length .binary32,
      demonLifetimeValues (fun _ state => state.lastReturn.value) life.demons⟩,
   ⟨"settled_error", .array demonLayout.length .binary32,
      demonLifetimeValues (fun _ state => state.lastError.value) life.demons⟩,
   wordArray "lifetime_option_started" life.options (·.started),
   wordArray "lifetime_option_completed" life.options (·.completed),
   wordArray "lifetime_option_duration" life.options (·.duration),
   wordArray "lifetime_option_end_reasons" (life.options.map (·.reasons)).flatten id,
   wordArray "lifetime_goal_attempts" life.goals (·.attempts),
   wordArray "lifetime_goal_successes" life.goals (·.successes),
   wordArray "lifetime_goal_steps" life.goals (·.steps),
   wordArray "lifetime_cycle_attempts" life.goalCycles.flatten (·.attempts),
   wordArray "lifetime_cycle_successes" life.goalCycles.flatten (·.successes),
   wordArray "lifetime_cycle_steps" life.goalCycles.flatten (·.steps)] ++ agreementTelemetry agent

end Acorn.Host.Viewer
