/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Control
import Acorn.Lifetime
import Acorn.Handcrafted.Signals
import Acorn.Handcrafted.FeatureProfile

/-!
# Current prediction/control composition

This boundary connects a frame's signal values to the maintained learned
transitions, for every world interface. It processes one primitive decision supplied
by the action-selection owner. `TemporalControl` supplies option/exploration scheduling and `Agent` owns
the complete receiver and its lifetime observations.
Feedback is read before updating demons; gain is observed after all consumers
use its previous value. Attempt boundaries alone do not clear this state.
-/
namespace Acorn.Handcrafted
open Acorn.Features

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
structure PredictionControl (interface : Interface) (profile : FeatureProfile) (criterion : Criterion) (dimension : Dimension) where
  /-- Criterion-indexed primitive control and host gain. -/
  control : PrimitiveControl criterion dimension interface.actions.word.toNat
  /-- Credit-policy identity cannot change independently of the immutable profile. -/
  creditMatches : creditKind control.credit = profile.credit
  /-- Every prediction learner of the layout, shared with lifecycle retirement. -/
  demons : DemonBank dimension interface.layout
  /-- Previous-step predictions for the next encoding. -/
  predictions : PredictionCache interface.layout
  /-- Last absolute errors in canonical order. -/
  errors : Vector Binary32 interface.layout.length
  /-- Observational accounting shares these exact prediction outputs. -/
  lifetime : Lifetime.Stats interface.layout

/-- Legal zero knowledge and cold feedback for every current profile and criterion. -/
def PredictionControl.initial (interface : Interface) (profile : FeatureProfile) (criterion : Criterion)
    (dimension : Dimension) :
    PredictionControl interface profile criterion dimension :=
  ⟨PrimitiveControl.initial _ _ _ profile.credit.initial,
    by cases profile.credit <;> rfl,
    DemonBank.initial _ _, PredictionCache.initial _, Vector.replicate _ .zero, Lifetime.Stats.initial _⟩

variable {interface : Interface} {profile : FeatureProfile} {criterion : Criterion} {dimension : Dimension}

/-- One already-selected primitive transition with its signal values already
evaluated: credit policy, then demons, then host gain. Frozen mode retains learned
state and only records predecessor presence. -/
def PredictionControl.advanceWith (state : PredictionControl interface profile criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (cumulants : Features.Cumulants interface.layout)
    (reward : Binary32) (action : Action interface.actions.word.toNat) (own : Bool)
    (clock : UInt64 := 0) : PredictionControl interface profile criterion dimension :=
  if profile.mode == .frozen then
    { state with control := state.control.finish false reward }
  else
    let credited := state.control.creditStep features action own reward
    let outputs := state.demons.step features cumulants
    ⟨credited.finish true reward,
      (credit_kind_preserved state.control features action own reward).trans state.creditMatches,
      outputs.bank, outputs.predictions, outputs.errors,
      state.lifetime.recordDemons clock cumulants outputs.predictions⟩

/-- One already-selected primitive transition: the signal values are evaluated once
from the frame and the delivered reward, then `advanceWith`. -/
def PredictionControl.advance (state : PredictionControl interface profile criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (action : Action interface.actions.word.toNat) (own : Bool) (clock : UInt64 := 0) :
    PredictionControl interface profile criterion dimension :=
  state.advanceWith features (signalValues obs reward) reward action own clock

/-- Frozen profiles preserve every demon learner and its prior prediction cache. -/
theorem PredictionControl.frozen_predictions (state : PredictionControl interface profile criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (action : Action interface.actions.word.toNat) (own : Bool) (frozen : profile.mode = .frozen) :
    (state.advance features obs reward action own).demons = state.demons ∧
    (state.advance features obs reward action own).predictions = state.predictions := by
  simp [PredictionControl.advance, PredictionControl.advanceWith, frozen]

end Acorn.Handcrafted
