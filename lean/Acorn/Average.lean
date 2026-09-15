/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.State

/-!
# Host reward-rate numeric state

Richard S. Sutton and Andrew G. Barto, *Reinforcement Learning: An Introduction*,
second edition, MIT Press (2018), section 10.3, Exercise 10.8, page 251:
https://www.incompleteideas.net/book/the-book-2nd.html.
The exercise admits a reward-residual update and prefers the TD-error variant.
The fixed horizon, host-transition ownership and projections here are Acorn's
PAR-15 integration. Neither finite storage nor the ideal EMA identity is a
convergence guarantee under persistent noise.
-/

namespace Acorn

/-- The independent host-transition lag budget used by the current tracker. -/
def gainTrackingHorizon : UInt32 := AcornSpec.Constants.gainTrackingHorizon

/-- Gain is derived from the same declared horizon in binary32 arithmetic. -/
def gainTrackingStep : Binary32 :=
  (Binary32.mk 0x3f800000).div (Binary32.ofUInt64 gainTrackingHorizon.toUInt64)

/-- The scalar tracker owns a rate admitted to its own reward interval. -/
structure AverageRewardTracker where
  /-- Stored rate, finite and in [0,1] independently of any weight domain. -/
  rate : RewardRate

/-- Initial zero-rate storage uses the ordinary state constructor. -/
def AverageRewardTracker.initial : AverageRewardTracker := ⟨RewardRate.project .zero⟩

/-- One host observation. Input projection and output projection both belong to
this same executable recurrence; arbitrary NaNs and infinities are admitted. -/
def AverageRewardTracker.observe (tracker : AverageRewardTracker) (rawReward : Binary32) :
    AverageRewardTracker :=
  let reward := RewardRate.project rawReward
  let delta := gainTrackingStep.mul (reward.value.sub tracker.rate.value)
  ⟨RewardRate.project (tracker.rate.value.add delta)⟩

/-- Restore accepts an already validated rate and preserves its storage word. -/
def AverageRewardTracker.restore (_tracker : AverageRewardTracker) (rate : RewardRate) :
    AverageRewardTracker := ⟨rate⟩

/-- Every actual observation write stays in the rate's own interval, for every
admitted state and raw reward; no finite-input or distribution hypothesis is used. -/
theorem average_observe_legal (tracker : AverageRewardTracker) (reward : Binary32) :
    rewardRange.Contains (tracker.observe reward).rate.value :=
  (tracker.observe reward).rate.legal

/-- Restoration is bit identity after admission, with no hidden normalization. -/
theorem average_restore_word (tracker : AverageRewardTracker) (rate : RewardRate) :
    (tracker.restore rate).rate.value = rate.value := rfl

/-- Ordered finite host observations, without a stored replay buffer. -/
def AverageRewardTracker.observeFrom (tracker : AverageRewardTracker) (rewards : List Binary32) :
    AverageRewardTracker := rewards.foldl AverageRewardTracker.observe tracker

/-- Any finite observation prefix composes through its exact intermediate state. -/
theorem average_observe_append (tracker : AverageRewardTracker) (first second : List Binary32) :
    tracker.observeFrom (first ++ second) = (tracker.observeFrom first).observeFrom second := by
  simp [AverageRewardTracker.observeFrom, List.foldl_append]

end Acorn
