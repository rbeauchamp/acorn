import Acorn.FeatureConstants
import Acorn.FeatureRefresh

namespace Acorn.Handcrafted
open Features

def declaredTester : Features.Tester where
  period := 10000
  positive := by decide
  bounded := by decide
  maturity := 1000
  decay := ⟨0x3f7d70a4⟩
  complement := ⟨0x3c23d70a⟩

inductive EvaluationMode where
  | final
  | frozen
  | withoutReachRelation
  | primitiveOnly
  deriving DecidableEq

inductive ControlCredit where
  | perStep
  | smdpCatchUp
  | noSpanCredit
  deriving DecidableEq

inductive RatePolicy where
  | declared
  | perLearner
  | shared
  | annealed
  deriving DecidableEq

inductive SubtaskPolicy where
  | learned
  | spatial
  deriving DecidableEq

structure FeatureProfile where
  mode : EvaluationMode
  credit : ControlCredit
  rate : RatePolicy
  subtasks : SubtaskPolicy
  deriving DecidableEq

def FeatureProfile.usesHierarchy (profile : FeatureProfile) : Bool := profile.mode != .primitiveOnly

def FeatureProfile.checkpointSupported (profile : FeatureProfile) : Bool :=
  profile.mode == .final && profile.credit == .perStep &&
    profile.rate == .declared && profile.subtasks == .learned

theorem FeatureProfile.checkpoint_iff (profile : FeatureProfile) :
    profile.checkpointSupported = true ↔ profile.mode = .final ∧ profile.credit = .perStep ∧
      profile.rate = .declared ∧ profile.subtasks = .learned := by
  simp [FeatureProfile.checkpointSupported, and_assoc]

def FeatureProfile.Resumable (profile : FeatureProfile) : Prop :=
  profile.mode = .final ∧ profile.credit = .perStep ∧ profile.rate = .declared ∧
    profile.subtasks = .learned

instance (profile : FeatureProfile) : Decidable profile.Resumable :=
  decidable_of_iff (profile.checkpointSupported = true) profile.checkpoint_iff

theorem FeatureProfile.decide_resumable (profile : FeatureProfile) :
    decide profile.Resumable = profile.checkpointSupported := by
  cases supported : profile.checkpointSupported with
  | true => exact decide_eq_true (profile.checkpoint_iff.mp supported)
  | false =>
    exact decide_eq_false fun resumable =>
      absurd (profile.checkpoint_iff.mpr resumable) (by rw [supported]; exact Bool.false_ne_true)

def FeatureProfile.interests (profile : FeatureProfile) (config : Features.Config) :
    Vector (Interest config) Acorn.FeatureConstants.skillCount :=
  Vector.ofFn fun slot => match profile.subtasks with
    | .learned => .learned .neutral
    | .spatial => .declared .spatialPotentials slot

def FeatureProfile.ranksSubtasks (profile : FeatureProfile) : Bool := profile.subtasks == .learned

end Acorn.Handcrafted
