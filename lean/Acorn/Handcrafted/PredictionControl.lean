import Acorn.Control
import Acorn.Lifetime
import Acorn.Handcrafted.Signals
import Acorn.Handcrafted.FeatureProfile

namespace Acorn.Handcrafted
open Acorn.Features

def ControlCredit.initial : ControlCredit → PrimitiveCredit
  | .perStep => .perStep
  | .smdpCatchUp => .catchUp .closed
  | .noSpanCredit => .noSpan

def creditKind : PrimitiveCredit → ControlCredit
  | .perStep => .perStep
  | .catchUp _ => .smdpCatchUp
  | .noSpan => .noSpanCredit

theorem credit_kind_preserved {criterion : Criterion} {dimension : Dimension} {actions : Nat}
    (state : PrimitiveControl criterion dimension actions) (features : SwiftTd.ActiveSet dimension)
    (action : Action actions) (own : Bool) (reward : Binary32) :
    creditKind (state.creditStep features action own reward).credit = creditKind state.credit := by
  cases h : state.credit <;> cases own <;>
    simp [PrimitiveControl.creditStep, h, creditKind]

structure PredictionControl (interface : Interface) (profile : FeatureProfile) (criterion : Criterion) (dimension : Dimension) where
  control : PrimitiveControl criterion dimension interface.actions.word.toNat
  creditMatches : creditKind control.credit = profile.credit
  demons : DemonBank dimension interface.layout
  predictions : PredictionCache interface.layout
  errors : Vector Binary32 interface.layout.length
  lifetime : Lifetime.Stats interface.layout

def PredictionControl.initial (interface : Interface) (profile : FeatureProfile) (criterion : Criterion)
    (dimension : Dimension) :
    PredictionControl interface profile criterion dimension :=
  ⟨PrimitiveControl.initial _ _ _ profile.credit.initial,
    by cases profile.credit <;> rfl,
    DemonBank.initial _ _, PredictionCache.initial _, Vector.replicate _ .zero, Lifetime.Stats.initial _⟩

variable {interface : Interface} {profile : FeatureProfile} {criterion : Criterion} {dimension : Dimension}

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

def PredictionControl.advance (state : PredictionControl interface profile criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (action : Action interface.actions.word.toNat) (own : Bool) (clock : UInt64 := 0) :
    PredictionControl interface profile criterion dimension :=
  state.advanceWith features (signalValues obs reward) reward action own clock

theorem PredictionControl.frozen_predictions (state : PredictionControl interface profile criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface) (reward : Binary32)
    (action : Action interface.actions.word.toNat) (own : Bool) (frozen : profile.mode = .frozen) :
    (state.advance features obs reward action own).demons = state.demons ∧
    (state.advance features obs reward action own).predictions = state.predictions := by
  simp [PredictionControl.advance, PredictionControl.advanceWith, frozen]

end Acorn.Handcrafted
