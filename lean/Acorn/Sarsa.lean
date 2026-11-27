import Acorn.FeatureConsumers
import Acorn.Average

namespace Acorn.Features

abbrev Action (actions : Nat) := Fin actions

def Action.admit (actions raw : Nat) : Option (Action actions) :=
  if h : raw < actions then some ⟨raw, h⟩ else none

theorem Action.admit_none (actions raw : Nat) :
    Action.admit actions raw = none ↔ actions ≤ raw := by
  simp [Action.admit]

variable {config : Acorn.Config} {dimension : Dimension} {actions : Nat}

def Controller.predictAllCosted (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) : Costed (Vector Binary32 actions) :=
  Costed.mapVector (fun learner => learner.state.linearPredictionCosted features)
    controller.learners

def Controller.predictAll (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) : Vector Binary32 actions :=
  (controller.predictAllCosted features).val

theorem Controller.predictAll_def (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) :
    controller.predictAll features =
      controller.learners.map (fun learner => learner.state.linearPrediction features) := rfl

def Controller.traceDecay (_controller : Controller config dimension actions) : Binary32 :=
  config.rule.gamma.mul config.lambda

def Controller.clearCosted (controller : Controller config dimension actions) :
    Costed (Controller config dimension actions) := do
  let learners ← Costed.mapVector (fun learner => learner.applyCosted .clear trivial)
    controller.learners
  Costed.op .controllerClose ⟨learners, .zero, .zero, false⟩

def Controller.clear (controller : Controller config dimension actions) :
    Controller config dimension actions :=
  controller.clearCosted.val

theorem Controller.clear_def (controller : Controller config dimension actions) :
    controller.clear =
      ⟨controller.learners.map (fun learner => learner.apply .clear trivial), .zero, .zero,
        false⟩ := rfl

def Managed.creditCosted (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) : Costed { result : Managed config dimension // result.phase = true } :=
  Costed.bind (Costed.attach (learner.applyCosted (.first delta vd decay) trivial)) fun credited =>
    Costed.charge .creditRestart <|
      if restart then
        Costed.bind (Costed.attach (credited.val.applyCosted .clear trivial)) fun cleared =>
          Costed.pure ⟨cleared.val, by rw [cleared.property]; rfl⟩
      else Costed.pure ⟨credited.val, by rw [credited.property]; rfl⟩

def Managed.credit (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) : { result : Managed config dimension // result.phase = true } :=
  (learner.creditCosted delta vd decay restart).val

theorem Managed.credit_def (learner : Managed config dimension) (delta vd decay : Binary32)
    (restart : Bool) :
    learner.credit delta vd decay restart =
      let credited := learner.apply (.first delta vd decay) trivial
      if restart then ⟨credited.apply .clear trivial, rfl⟩ else ⟨credited, rfl⟩ := by
  unfold Managed.credit Managed.creditCosted
  cases restart <;> rfl

def Controller.creditStepCosted (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) : Costed (Controller config dimension actions) :=
  let ⟨learners, _, vDelta, restart⟩ := controller
  Costed.bind (detachedUpdateCosted learners action fun learner =>
      Costed.bind (Costed.attach (learner.creditCosted delta vDelta decay restart)) fun chosen =>
        Costed.bind (Costed.attach (chosen.val.val.state.learnSecondLoopCosted config features .zero))
          fun second => Costed.pure (⟨second.val.1, false, by
            rw [second.property]
            exact .transition (.second features .zero) chosen.val.property chosen.val.val.admitted⟩,
            second.val.2))
    fun taken =>
      Costed.bind (Costed.mapFinIdx taken.1 fun index learner _ =>
          Costed.ite (index = action.val) (fun _ => Costed.pure learner) fun _ =>
            Costed.bind (learner.creditCosted delta vDelta decay restart) fun credited =>
              Costed.pure credited.val)
        fun rows => Costed.op .creditClose ⟨rows, lag, taken.2, false⟩

def Controller.creditStep (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) : Controller config dimension actions :=
  (controller.creditStepCosted features action lag delta decay).val

theorem Controller.creditStep_def (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) :
    controller.creditStep features action lag delta decay =
      let ⟨learners, _, vDelta, restart⟩ := controller
      let taken := detachedUpdate learners action fun learner =>
        let chosen := learner.credit delta vDelta decay restart
        let second := chosen.val.state.learnSecondLoop config features .zero
        (⟨second.1, false,
            .transition (.second features .zero) chosen.property chosen.val.admitted⟩, second.2)
      ⟨taken.1.mapFinIdx fun index learner _ =>
          if index = action.val then learner else (learner.credit delta vDelta decay restart).val,
        lag, taken.2, false⟩ := by
  cases controller
  rfl

theorem Controller.creditStep_eq (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (lag delta decay : Binary32) :
    controller.creditStep features action lag delta decay =
      let rows := controller.learners.map (fun learner =>
        learner.credit delta controller.vDelta decay controller.restartPending)
      let chosen := rows.get action
      let second := chosen.val.state.learnSecondLoop config features .zero
      let updated : Managed config dimension :=
        ⟨second.1, false, .transition (.second features .zero) chosen.property chosen.val.admitted⟩
      ⟨(rows.map Subtype.val).set action.val updated action.isLt, lag, second.2, false⟩ := by
  cases controller with
  | mk learners vOld vDelta restart =>
    have row : (learners.map fun learner => learner.credit delta vDelta decay restart).get action =
        (learners.get action).credit delta vDelta decay restart :=
      Vector.getElem_map _ action.isLt
    simp only [Controller.creditStep_def, detachedUpdate_eq, row]
    congr 1
    apply Vector.ext
    intro position inside
    by_cases here : action.val = position
    · subst here
      simp only [Vector.getElem_mapFinIdx, Vector.getElem_set_self, ite_true]
    · have there : ¬position = action.val := fun same => here same.symm
      simp only [Vector.getElem_mapFinIdx, Vector.getElem_map,
        Vector.getElem_set_ne action.isLt inside here, there, ite_false]

def Controller.valuesStepCosted (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    Costed (Controller config dimension actions) :=
  Costed.charge .valuesOpen <| controller.creditStepCosted features action (values.get action)
    ((reward.add (bootstrap.mul (values.get action))).sub controller.vOld) decay

def Controller.valuesStep (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    Controller config dimension actions :=
  (controller.valuesStepCosted features values action reward bootstrap decay).val

theorem Controller.valuesStep_def (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    controller.valuesStep features values action reward bootstrap decay =
      controller.creditStep features action (values.get action)
        ((reward.add (bootstrap.mul (values.get action))).sub controller.vOld) decay := rfl

def Controller.releaseCosted (controller : Controller config dimension actions) :
    Costed (Controller config dimension actions) := do
  let learners ← Costed.mapVector (fun learner => learner.applyCosted .release trivial)
    controller.learners
  Costed.op .controllerClose { controller with learners := learners, vDelta := .zero }

def Controller.release (controller : Controller config dimension actions) :
    Controller config dimension actions :=
  controller.releaseCosted.val

theorem Controller.release_def (controller : Controller config dimension actions) :
    controller.release =
      { controller with
        learners := controller.learners.map (fun learner => learner.apply .release trivial)
        vDelta := .zero } := rfl

def Controller.startStepCosted (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (lag : Binary32) :
    Costed (Controller config dimension actions) := do
  let released ← controller.releaseCosted
  released.creditStepCosted features action lag .zero .zero

def Controller.startStep (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (lag : Binary32) :
    Controller config dimension actions :=
  (controller.startStepCosted features action lag).val

theorem Controller.startStep_def (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (lag : Binary32) :
    controller.startStep features action lag =
      controller.release.creditStep features action lag .zero .zero := rfl

def Controller.stopStepCosted (controller : Controller config dimension actions)
    (delta : Binary32) : Costed (Controller config dimension actions) :=
  let ⟨learners, _, vDelta, restart⟩ := controller
  Costed.bind (Costed.mapVector (fun learner =>
      Costed.bind (learner.creditCosted delta vDelta .zero restart) fun credited =>
        credited.val.applyCosted .release trivial) learners)
    fun rows => Costed.op .controllerClose ⟨rows, .zero, .zero, false⟩

def Controller.stopStep (controller : Controller config dimension actions) (delta : Binary32) :
    Controller config dimension actions :=
  (controller.stopStepCosted delta).val

theorem Controller.stopStep_def (controller : Controller config dimension actions)
    (delta : Binary32) :
    controller.stopStep delta =
      let ⟨learners, _, vDelta, restart⟩ := controller
      ⟨learners.map (fun learner =>
        (learner.credit delta vDelta .zero restart).val.apply .release trivial), .zero, .zero,
        false⟩ := by
  cases controller
  rfl

theorem Controller.stopStep_eq (controller : Controller config dimension actions)
    (delta : Binary32) :
    controller.stopStep delta =
      ⟨controller.learners.map (fun learner =>
        (learner.credit delta controller.vDelta .zero controller.restartPending).val.apply
          .release trivial), .zero, .zero, false⟩ := by
  cases controller
  rfl

def Controller.stepCosted (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (reward : Binary32) :
    Costed (Controller config dimension actions × Vector Binary32 actions) := do
  let values ← controller.predictAllCosted features
  let next ← controller.valuesStepCosted features values action reward config.rule.gamma
    controller.traceDecay
  Costed.pure (next, values)

def Controller.step (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (reward : Binary32) :
    Controller config dimension actions × Vector Binary32 actions :=
  (controller.stepCosted features action reward).val

theorem Controller.step_def (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (reward : Binary32) :
    controller.step features action reward =
      let values := controller.predictAll features
      (controller.valuesStep features values action reward config.rule.gamma
        controller.traceDecay, values) := rfl

def Controller.smdpStepCosted (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (reward : Binary32) (duration : UInt32) :
    Costed (Controller config dimension actions × Vector Binary32 actions) := do
  let values ← controller.predictAllCosted features
  let next ← Costed.charge .policyOpen <| controller.valuesStepCosted features values action
    reward (Portable.pow config.rule.gamma duration) (Portable.pow controller.traceDecay duration)
  Costed.pure (next, values)

def Controller.smdpStep (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (reward : Binary32) (duration : UInt32) :
    Controller config dimension actions × Vector Binary32 actions :=
  (controller.smdpStepCosted features action reward duration).val

theorem Controller.smdpStep_def (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions)
    (reward : Binary32) (duration : UInt32) :
    controller.smdpStep features action reward duration =
      let values := controller.predictAll features
      (controller.valuesStep features values action reward
        (Portable.pow config.rule.gamma duration) (Portable.pow controller.traceDecay duration),
        values) := rfl

def Controller.closeStepCosted (controller : Controller config dimension actions)
    (reward continuation : Binary32) (duration : UInt32) :
    Costed (Controller config dimension actions) := do
  let discount ← Costed.op .policyOpen (Portable.pow config.rule.gamma duration)
  let delta := (reward.add (discount.mul continuation)).sub controller.vOld
  Costed.charge .learnerError (controller.stopStepCosted delta)

def Controller.closeStep (controller : Controller config dimension actions)
    (reward continuation : Binary32) (duration : UInt32) :
    Controller config dimension actions :=
  (controller.closeStepCosted reward continuation duration).val

theorem Controller.closeStep_def (controller : Controller config dimension actions)
    (reward continuation : Binary32) (duration : UInt32) :
    controller.closeStep reward continuation duration =
      controller.stopStep
        ((reward.add ((Portable.pow config.rule.gamma duration).mul continuation)).sub
          controller.vOld) := rfl

def Controller.terminalCosted (controller : Controller config dimension actions)
    (reward : Binary32) : Costed (Controller config dimension actions) :=
  let decay := controller.traceDecay
  let ⟨learners, vOld, vDelta, restart⟩ := controller
  let delta := reward.sub vOld
  Costed.charge .learnerError <| Costed.bind (Costed.mapVector
      (fun learner => learner.applyCosted (.first delta vDelta decay) trivial) learners)
    fun credited => (Controller.mk credited vOld vDelta restart).clearCosted

def Controller.terminal (controller : Controller config dimension actions) (reward : Binary32) :
    Controller config dimension actions :=
  (controller.terminalCosted reward).val

theorem Controller.terminal_def (controller : Controller config dimension actions)
    (reward : Binary32) :
    controller.terminal reward =
      let decay := controller.traceDecay
      let ⟨learners, vOld, vDelta, restart⟩ := controller
      let delta := reward.sub vOld
      let credited := learners.map
        (fun learner => learner.apply (.first delta vDelta decay) trivial)
      (Controller.mk credited vOld vDelta restart).clear := by
  cases controller
  rfl

theorem Controller.terminal_eq (controller : Controller config dimension actions)
    (reward : Binary32) :
    controller.terminal reward =
      (Controller.mk (controller.learners.map fun learner =>
          learner.apply (.first (reward.sub controller.vOld) controller.vDelta
            controller.traceDecay) trivial)
        controller.vOld controller.vDelta controller.restartPending).clear := by
  cases controller
  rfl

def Controller.stepRaw (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (raw : Nat) (reward : Binary32) :
    Option (Controller config dimension actions × Vector Binary32 actions) :=
  (Action.admit actions raw).map (fun action => controller.step features action reward)

theorem Controller.stepRaw_refuses (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (raw : Nat) (reward : Binary32)
    (outside : actions ≤ raw) : controller.stepRaw features raw reward = none := by
  simp [Controller.stepRaw, Action.admit, Nat.not_lt.mpr outside]

theorem Controller.step_observation (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) (reward : Binary32) :
    (controller.step features action reward).2 = controller.predictAll features := rfl

theorem Controller.valuesStep_lag (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    (controller.valuesStep features values action reward bootstrap decay).vOld = values.get action := by
  rw [Controller.valuesStep_def, Controller.creditStep_eq]

theorem Controller.valuesStep_eq_creditStep (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    controller.valuesStep features values action reward bootstrap decay =
      controller.creditStep features action (values.get action)
        ((reward.add (bootstrap.mul (values.get action))).sub controller.vOld) decay := rfl

theorem Controller.stopStep_lags (controller : Controller config dimension actions)
    (delta : Binary32) :
    (controller.stopStep delta).vOld = .zero ∧ (controller.stopStep delta).vDelta = .zero ∧
    (controller.stopStep delta).restartPending = false := by
  rw [Controller.stopStep_eq]
  exact ⟨rfl, rfl, rfl⟩

theorem Controller.terminal_lags (controller : Controller config dimension actions) (reward : Binary32) :
    (controller.terminal reward).vOld = .zero ∧
    (controller.terminal reward).vDelta = .zero ∧
    (controller.terminal reward).restartPending = false := by
  rw [Controller.terminal_eq]
  exact ⟨rfl, rfl, rfl⟩

def Criterion.center (criterion : Criterion) (reward : Binary32) (duration : UInt32)
    (rate : RewardRate) : Binary32 :=
  match criterion with
  | .discounted => reward
  | .differential => reward.sub ((Binary32.ofUInt64 duration.toUInt64).mul rate.value)

def Criterion.observe (criterion : Criterion) (tracker : AverageRewardTracker)
    (pending learning : Bool) (reward : Binary32) : AverageRewardTracker :=
  if pending && learning && criterion == .differential then tracker.observe reward else tracker

theorem Criterion.observe_initial (criterion : Criterion) (tracker : AverageRewardTracker)
    (learning : Bool) (reward : Binary32) : criterion.observe tracker false learning reward = tracker := by
  simp [Criterion.observe]

end Acorn.Features
