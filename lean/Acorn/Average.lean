import Acorn.State

namespace Acorn

def gainTrackingHorizon : UInt32 := Acorn.Constants.gainTrackingHorizon

def gainTrackingStep : Binary32 :=
  (Binary32.mk 0x3f800000).div (Binary32.ofUInt64 gainTrackingHorizon.toUInt64)

structure AverageRewardTracker where
  rate : RewardRate

def AverageRewardTracker.initial : AverageRewardTracker := ⟨RewardRate.project .zero⟩

def AverageRewardTracker.observe (tracker : AverageRewardTracker) (rawReward : Binary32) :
    AverageRewardTracker :=
  let reward := RewardRate.project rawReward
  let delta := gainTrackingStep.mul (reward.value.sub tracker.rate.value)
  ⟨RewardRate.project (tracker.rate.value.add delta)⟩

theorem average_observe_legal (tracker : AverageRewardTracker) (reward : Binary32) :
    rewardRange.Contains (tracker.observe reward).rate.value :=
  (tracker.observe reward).rate.legal

def AverageRewardTracker.observeFrom (tracker : AverageRewardTracker) (rewards : List Binary32) :
    AverageRewardTracker := rewards.foldl AverageRewardTracker.observe tracker

theorem average_observe_append (tracker : AverageRewardTracker) (first second : List Binary32) :
    tracker.observeFrom (first ++ second) = (tracker.observeFrom first).observeFrom second := by
  simp [AverageRewardTracker.observeFrom, List.foldl_append]

end Acorn
