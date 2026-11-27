import Acorn.Policy

namespace Acorn.Features

structure CreditGap where
  steps : UInt8
  reward : Binary32

def CreditGap.closed : CreditGap := ⟨0, .zero⟩

def CreditGap.accumulate (gap : CreditGap) (reward gamma : Binary32) : CreditGap :=
  { gap with reward := gap.reward.add (reward.mul (Portable.pow gamma gap.steps.toUInt32)) }

def CreditGap.skip (gap : CreditGap) : CreditGap :=
  { gap with steps := if gap.steps == 255 then 255 else gap.steps + 1 }

def CreditGap.close (gap : CreditGap) : Binary32 × UInt32 := (gap.reward, gap.steps.toUInt32 + 1)

inductive PrimitiveCredit where
  | perStep
  | catchUp (gap : CreditGap)
  | noSpan

structure PrimitiveControl (criterion : Criterion) (dimension : Dimension) (actions : Nat) where
  controller : Controller (criterion.config .control) dimension actions
  credit : PrimitiveCredit
  average : AverageRewardTracker
  pending : Bool

def PrimitiveControl.initial (criterion : Criterion) (dimension : Dimension) (actions : Nat)
    (credit : PrimitiveCredit) : PrimitiveControl criterion dimension actions :=
  ⟨Controller.initial _ _ _, credit, .initial, false⟩

variable {criterion : Criterion} {dimension : Dimension} {actions : Nat}

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

def PrimitiveControl.finish (state : PrimitiveControl criterion dimension actions)
    (learning : Bool) (reward : Binary32) : PrimitiveControl criterion dimension actions :=
  { state with average := criterion.observe state.average state.pending learning reward, pending := true }

theorem PrimitiveControl.credit_preserves_clock (state : PrimitiveControl criterion dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (own : Bool) (reward : Binary32) :
    (state.creditStep features action own reward).average = state.average ∧
    (state.creditStep features action own reward).pending = state.pending := by
  unfold creditStep
  split <;> first | exact ⟨rfl, rfl⟩ | (split <;> exact ⟨rfl, rfl⟩)

theorem PrimitiveControl.finish_preserves_credit (state : PrimitiveControl criterion dimension actions)
    (learning : Bool) (reward : Binary32) :
    (state.finish learning reward).controller = state.controller ∧
    (state.finish learning reward).credit = state.credit := ⟨rfl, rfl⟩

theorem CreditGap.close_duration (gap : CreditGap) :
    1 ≤ gap.close.2.toNat ∧ gap.close.2.toNat ≤ 256 := by
  have bound := gap.steps.toNat_lt
  simp only [CreditGap.close, UInt32.toNat_add, UInt8.toNat_toUInt32, UInt32.toNat_ofNat]
  omega

end Acorn.Features
