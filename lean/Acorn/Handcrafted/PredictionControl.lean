/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Control
import Acorn.Lifetime
import Acorn.Handcrafted.Cumulants
import Acorn.Handcrafted.FeatureProfile

/-!
# Current host prediction/control composition

This boundary connects D5 signals and D1 encoding to the maintained learned
transitions. It processes one primitive decision supplied by the action-selection
owner. `TemporalControl` supplies option/exploration scheduling and `Agent` owns
the complete receiver and its lifetime observations.
Feedback is read before updating demons; gain is observed after all consumers
use its previous value. Attempt boundaries alone do not clear this state.
-/
namespace Acorn.Handcrafted
open Acorn.Features Acorn.Host

/-- Immutable profile chooses the initial primitive-credit state. -/
def ControlCredit.initial : ControlCredit → PrimitiveCredit
  | .perStep => .perStep
  | .smdpCatchUp => .catchUp .closed
  | .noSpanCredit => .noSpan

/-- The credit tag is observed without interpreting its accumulated reward. -/
def creditKind : PrimitiveCredit → ControlCredit
  | .perStep => .perStep
  | .catchUp _ => .smdpCatchUp
  | .noSpan => .noSpanCredit

/-- Updates preserve the constructed credit policy across every own/option branch. -/
theorem credit_kind_preserved {criterion : Criterion} {dimension : Dimension} {actions : Nat}
    (state : PrimitiveControl criterion dimension actions) (features : SwiftTd.ActiveSet dimension)
    (action : Action actions) (own : Bool) (reward : Binary32) :
    creditKind (state.creditStep features action own reward).credit = creditKind state.credit := by
  cases h : state.credit <;> cases own <;>
    simp [PrimitiveControl.creditStep, h, creditKind]

/-- Persistent local prediction/control state under all current profile/criterion combinations. -/
structure PredictionControl (profile : FeatureProfile) (criterion : Criterion) (dimension : Dimension) where
  /-- Criterion-indexed primitive control and host gain. -/
  control : PrimitiveControl criterion dimension Acorn.FeatureConstants.primitiveCount
  /-- Credit-policy identity cannot change independently of the immutable profile. -/
  creditMatches : creditKind control.credit = profile.credit
  /-- All eleven current prediction learners, shared with lifecycle retirement. -/
  demons : DemonBank dimension demonLayout
  /-- Previous-step predictions for the next encoding. -/
  predictions : PredictionCache demonLayout
  /-- Last absolute errors in canonical order. -/
  errors : Vector Binary32 demonLayout.length
  /-- Observational accounting shares these exact prediction outputs. -/
  lifetime : Lifetime.Stats demonLayout

/-- Legal zero knowledge and cold feedback for every current profile and criterion. -/
def PredictionControl.initial (profile : FeatureProfile) (criterion : Criterion) (dimension : Dimension) :
    PredictionControl profile criterion dimension :=
  ⟨PrimitiveControl.initial _ _ _ profile.credit.initial,
    by cases profile.credit <;> rfl,
    DemonBank.initial _ _, PredictionCache.initial _, Vector.replicate _ .zero, Lifetime.Stats.initial _⟩

variable {profile : FeatureProfile} {criterion : Criterion} {dimension : Dimension}

/-- Encode using the stored previous predictions and this immutable profile. -/
def PredictionControl.encode (state : PredictionControl profile criterion dimension)
    {config : Features.Config} (bank : Bank patchShape config) (obs : Observation) :
    SwiftTd.ActiveSet dimension :=
  profile.encode dimension bank obs (feedbackPredictions state.predictions)

/-- One already-selected primitive transition: credit policy, then demons, then
host gain. Frozen mode retains learned state and only records predecessor presence. -/
def PredictionControl.advance (state : PredictionControl profile criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Observation) (reward : Binary32)
    (action : Action Acorn.FeatureConstants.primitiveCount) (own : Bool) (clock : UInt64 := 0) :
    PredictionControl profile criterion dimension :=
  if profile.mode == .frozen then
    { state with control := state.control.finish false reward }
  else
    let credited := state.control.creditStep features action own reward
    let cumulants := evaluateCumulants cumulantOrder obs reward
    let outputs := state.demons.step features cumulants
    ⟨credited.finish true reward,
      (credit_kind_preserved state.control features action own reward).trans state.creditMatches,
      outputs.bank, outputs.predictions, outputs.errors,
      state.lifetime.recordDemons clock cumulants outputs.predictions⟩

/-- Public action refusal precedes encoding and any state transition. -/
def PredictionControl.advanceRaw (state : PredictionControl profile criterion dimension)
    {config : Features.Config} (bank : Bank patchShape config) (obs : Observation)
    (reward : Binary32) (raw : Nat) (own : Bool) : Option (PredictionControl profile criterion dimension) :=
  (Action.admit Acorn.FeatureConstants.primitiveCount raw).map fun action =>
    state.advance (state.encode bank obs) obs reward action own

/-- Rejection produces no replacement even with arbitrary reward and sensory words. -/
theorem PredictionControl.raw_refusal (state : PredictionControl profile criterion dimension)
    {config : Features.Config} (bank : Bank patchShape config) (obs : Observation)
    (reward : Binary32) (raw : Nat) (own : Bool) (outside : Acorn.FeatureConstants.primitiveCount ≤ raw) :
    state.advanceRaw bank obs reward raw own = none := by
  simp [PredictionControl.advanceRaw, Action.admit, Nat.not_lt.mpr outside]

/-- Recursive encoding reads precisely the old cache, before current demon writes. -/
theorem PredictionControl.feedback_input (state : PredictionControl profile criterion dimension)
    {config : Features.Config} (bank : Bank patchShape config) (obs : Observation) :
    state.encode bank obs = profile.encode dimension bank obs (feedbackPredictions state.predictions) := rfl

/-- Frozen profiles preserve every demon learner and its prior prediction cache. -/
theorem PredictionControl.frozen_predictions (state : PredictionControl profile criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Observation) (reward : Binary32)
    (action : Action Acorn.FeatureConstants.primitiveCount) (own : Bool) (frozen : profile.mode = .frozen) :
    (state.advance features obs reward action own).demons = state.demons ∧
    (state.advance features obs reward action own).predictions = state.predictions := by
  simp [PredictionControl.advance, frozen]

end Acorn.Handcrafted
