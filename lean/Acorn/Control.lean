/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Policy

/-!
# Primitive control credit and host gain clock

The current per-step, deferred SMDP and no-span credit policies share the real
Sarsa controller. Sutton, Precup & Singh, *Between MDPs and semi-MDPs*, Artificial
Intelligence 112 (1999), §6, pp. 204–205, describes intra-option learning; Acorn's
PAR-9 uses executed-action Sarsa rather than the max-bootstrap update.
Sutton & Barto, *Reinforcement Learning*, MIT Press (2018), §10.3, Exercise 10.8,
owns the reward-residual gain variant. The independently fixed host-time gain
and its use across layers are Acorn's PAR-15 integration.
-/
namespace Acorn.Features

/-- Current deferred primitive credit retains a byte of skipped steps. -/
structure CreditGap where
  /-- Saturating count of skipped primitive updates. -/
  steps : UInt8
  /-- Raw ordered discounted reward sum. -/
  reward : Binary32

/-- A closed gap has no skipped steps or accumulated reward. -/
def CreditGap.closed : CreditGap := ⟨0, .zero⟩

/-- Add a reward at the discount of the already elapsed skipped span. -/
def CreditGap.accumulate (gap : CreditGap) (reward gamma : Binary32) : CreditGap :=
  { gap with reward := gap.reward.add (reward.mul (Portable.pow gamma gap.steps.toUInt32)) }

/-- Skipping saturates at the storage boundary, never wraps. -/
def CreditGap.skip (gap : CreditGap) : CreditGap :=
  { gap with steps := if gap.steps == 255 then 255 else gap.steps + 1 }

/-- Close includes the acting step; widening precedes addition. -/
def CreditGap.close (gap : CreditGap) : Binary32 × UInt32 := (gap.reward, gap.steps.toUInt32 + 1)

/-- Current credit alternatives, with deferred state only where used. -/
inductive PrimitiveCredit where
  /-- Ordinary one-step credit under both own and option actions. -/
  | perStep
  /-- Accumulate option steps and repay at the next own decision. -/
  | catchUp (gap : CreditGap)
  /-- Historical ablation omits only option-executed credit. -/
  | noSpan

/-- Primitive learner, credit state and the one host-transition gain clock. -/
structure PrimitiveControl (criterion : Criterion) (dimension : Dimension) (actions : Nat) where
  /-- Same lifecycle-owned controller, with criterion fixed by its type. -/
  controller : Controller (criterion.config .control) dimension actions
  /-- Declared policy and its possible deferred credit. -/
  credit : PrimitiveCredit
  /-- One gain observation per actual learned host transition. -/
  average : AverageRewardTracker
  /-- Whether a preceding action has actually been requested. -/
  pending : Bool

/-- Initialize one primitive controller without an invented predecessor transition. -/
def PrimitiveControl.initial (criterion : Criterion) (dimension : Dimension) (actions : Nat)
    (credit : PrimitiveCredit) : PrimitiveControl criterion dimension actions :=
  ⟨Controller.initial _ _ _, credit, .initial, false⟩

variable {criterion : Criterion} {dimension : Dimension} {actions : Nat}

/-- Discharge the current credit policy using the old host gain. Gain observation
is separate so every hierarchy member can consume the same pre-update value. -/
def PrimitiveControl.creditStep (state : PrimitiveControl criterion dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (own : Bool)
    (reward : Binary32) : PrimitiveControl criterion dimension actions :=
  match state.credit with
  | .perStep => { state with controller :=
      (state.controller.step features action (criterion.center reward 1 state.average.rate)).1 }
  | .noSpan => if own then { state with controller :=
      (state.controller.step features action (criterion.center reward 1 state.average.rate)).1 } else state
  | .catchUp gap =>
    let gap := gap.accumulate reward criterion.rule.gamma
    if own then
      let owed := gap.close
      let controller := (state.controller.smdpStep features action
        (criterion.center owed.1 owed.2 state.average.rate) owed.2).1
      { state with controller := controller, credit := .catchUp .closed }
    else { state with credit := .catchUp gap.skip }

/-- Finish a host step only after all learning consumers have read the old gain. -/
def PrimitiveControl.finish (state : PrimitiveControl criterion dimension actions)
    (learning : Bool) (reward : Binary32) : PrimitiveControl criterion dimension actions :=
  { state with average := criterion.observe state.average state.pending learning reward, pending := true }

/-- Credit itself preserves the gain snapshot and the host-transition clock. -/
theorem PrimitiveControl.credit_preserves_clock (state : PrimitiveControl criterion dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (own : Bool) (reward : Binary32) :
    (state.creditStep features action own reward).average = state.average ∧
    (state.creditStep features action own reward).pending = state.pending := by
  unfold creditStep
  split <;> first | exact ⟨rfl, rfl⟩ | (split <;> exact ⟨rfl, rfl⟩)

/-- Host completion never changes controller knowledge or its credit span. -/
theorem PrimitiveControl.finish_preserves_credit (state : PrimitiveControl criterion dimension actions)
    (learning : Bool) (reward : Binary32) :
    (state.finish learning reward).controller = state.controller ∧
    (state.finish learning reward).credit = state.credit := ⟨rfl, rfl⟩

/-- Closing any admitted gap hands off at most 256 primitive steps. -/
theorem CreditGap.close_duration (gap : CreditGap) :
    1 ≤ gap.close.2.toNat ∧ gap.close.2.toNat ≤ 256 := by
  have bound := gap.steps.toNat_lt
  simp only [CreditGap.close, UInt32.toNat_add, UInt8.toNat_toUInt32, UInt32.toNat_ofNat]
  omega

end Acorn.Features
