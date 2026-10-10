/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.StepParts
import AcornVerif.Resource.EncodeWork
import AcornVerif.Resource.PlanWork
import AcornVerif.Resource.RefreshWork

/-!
# Work of selection

Twins of the dispatch of `Acorn.Handcrafted.TemporalControl` with the model operations and
the planning boundary that `TemporalControl.select` passes. Each twin is the executed
operation's value with the work of a run that follows the operation's control flow: the run
tests the conditions the operation tests, on the values the executed definitions compute,
and charges the twin of every operation it calls. Where the executed operation takes an
option out of its table so that the runtime can reuse its storage (`detachedUpdate`), the
run follows the listed composition the repository proves equal to it
(`TemporalControl.dispatchMeta_eq`, `TemporalControl.stepOption_eq`,
`TemporalControl.closeOption_eq`).
-/

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension}

/-! ## Rates and the value function -/

/-- The costed run of `RateState.controller` and `RateState.skill`: the learner rate the
policy resolves, if any. -/
def rateRun {policy : RatePolicy} (rate : RateState policy) (own primitive : Costed Unit) :
    Costed Unit :=
  match rate with
  | .declared => Costed.pure ()
  | .perLearner => own
  | .shared => primitive
  | .annealed _ => Costed.pure ()

theorem rateRun_work {policy : RatePolicy} (rate : RateState policy) (own primitive : Costed Unit)
    (bound : Nat) (ownFits : own.work ≤ bound) (primitiveFits : primitive.work ≤ bound) :
    (rateRun rate own primitive).work ≤ bound := by
  cases rate
  · exact Nat.zero_le _
  · exact ownFits
  · exact primitiveFits
  · exact Nat.zero_le _

/-- Twin of `TemporalControl.primitiveRate`. -/
def primitiveRate (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    Costed SwiftTd.ExploreRate :=
  exploreRate (count := interface.actions) κ state.runtime.lifecycle.consumers.control

/-- Twin of `TemporalControl.metaRate`. -/
def metaRate (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    Costed SwiftTd.ExploreRate :=
  Costed.via state.metaRate (rateRun state.rate
    (Costed.discard (exploreRate (count := metaCount) κ
      state.runtime.lifecycle.consumers.metaController))
    (Costed.discard (primitiveRate κ state)))

/-- Bound of any controller rate of a state. -/
abbrev metaRateBound (κ : Costs) (rows capacity : Nat) : Nat :=
  rateBound κ metaCount.word.toNat capacity + rateBound κ rows capacity

theorem metaRate_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    (metaRate κ state).work ≤ metaRateBound κ interface.actions.word.toNat dimension.capacity :=
  rateRun_work _ _ _ _ (Nat.le_trans (exploreRate_work κ _) (Nat.le_add_right _ _))
    (Nat.le_trans (exploreRate_work κ _) (Nat.le_add_left _ _))

/-- Twin of `TemporalControl.controlRate`. -/
def controlRate (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    Costed SwiftTd.ExploreRate :=
  Costed.via state.controlRate (rateRun state.rate (Costed.discard (primitiveRate κ state))
    (Costed.discard (primitiveRate κ state)))

theorem controlRate_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    (controlRate κ state).work ≤ metaRateBound κ interface.actions.word.toNat dimension.capacity :=
  rateRun_work _ _ _ _ (Nat.le_trans (exploreRate_work κ _) (Nat.le_add_left _ _))
    (Nat.le_trans (exploreRate_work κ _) (Nat.le_add_left _ _))

/-- Twin of `TemporalControl.skillRate`. -/
def skillSource (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    Costed ConsumerRate :=
  Costed.via state.skillRate (rateRun state.rate (Costed.pure ())
    (Costed.discard (primitiveRate κ state)))

theorem skillSource_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    (skillSource κ state).work ≤ metaRateBound κ interface.actions.word.toNat dimension.capacity :=
  rateRun_work _ _ _ _ (Nat.zero_le _)
    (Nat.le_trans (exploreRate_work κ _) (Nat.le_add_left _ _))

/-- Twin of `TemporalControl.valueFunction`. -/
def valueFunction (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    Costed (ValueFunction criterion dimension) := do
  let rate ← metaRate κ state
  Costed.pure ⟨state.runtime.lifecycle.consumers.metaController, rate⟩

theorem valueFunction_val (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    (valueFunction κ state).val = state.valueFunction := rfl

theorem valueFunction_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    (valueFunction κ state).work ≤
      metaRateBound κ interface.actions.word.toNat dimension.capacity :=
  Nat.le_trans (Costed.bind_work_le (metaRate_work κ state) fun _ => Nat.le_refl 0)
    (Nat.le_of_eq (Nat.add_zero _))

/-! ## The operations of selection -/

/-- The costed run of `TemporalControl.prepareSelection`: the rate advance and the owed meta
reward, then each option model's prediction under the current value function. -/
def prepareRun (κ : Costs) (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) : Costed Unit :=
  let state := { state with rate := state.rate.advance }
  let state := if profile.usesHierarchy && profile.mode != .frozen then
    state.withGap (state.gap.accumulate reward criterion.rule.gamma) else state
  Costed.charge (κ .prepare) (Costed.ite (profile.usesHierarchy = true)
    (Costed.discard (Costed.mapVector (κ .visit)
      (fun skill => do
        let value ← valueFunction κ state
        let prediction ← predict κ skill.model value features ⟨0, by decide⟩
        Costed.op (κ .read) prediction.cache)
      state.runtime.lifecycle.consumers.skills))
    (Costed.pure ()))

/-- Bound of selection's preparation over `width` features. -/
abbrev prepareBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  κ .prepare + Acorn.FeatureConstants.skillCount * (κ .visit + (metaRateBound κ rows capacity +
    (predictBound κ positions width + κ .read)))

theorem prepareRun_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    (prepareRun κ state features reward).work ≤
      prepareBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length :=
  Costed.charge_work_le (Costed.ite_work_bound _ (Costed.discard_work_le
    (Costed.mapVector_work_le _ _ _ _ fun skill _ =>
      Costed.bind_work_le (valueFunction_work κ _) fun value =>
        Costed.bind_work_le (predict_work κ skill.model value features _) fun _ =>
          Nat.le_refl _)) (Nat.zero_le _))

/-- The costed run of `TemporalControl.serve`: a committed run with a step left repeats its
action and reports both controllers' values and a point mass. -/
def serveRun (κ : Costs) (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) : Costed Unit :=
  match state.runtime.references.phase with
  | .exploring committed =>
    match committed.run.serve with
    | none => Costed.pure ()
    | some (action, _) => do
      Costed.ite (profile.usesHierarchy = true)
        (Costed.discard (Costed.replicate (κ .visit) Acorn.FeatureConstants.skillCount
          Binary32.zero))
        (Costed.pure ())
      Costed.discard (predictAll κ state.runtime.lifecycle.consumers.control features)
      Costed.ite (profile.usesHierarchy = true)
        (Costed.discard (predictAll κ state.runtime.lifecycle.consumers.metaController features))
        (Costed.discard (Costed.replicate (κ .visit) metaCount.word.toNat Binary32.zero))
      Costed.discard (servedProbabilities κ action)
      Costed.op (κ .serve) ()
  | .idle | .option _ _ => Costed.pure ()

/-- Bound of a served step over `width` features. -/
abbrev serveBound (κ : Costs) (rows width : Nat) : Nat :=
  Acorn.FeatureConstants.skillCount * κ .visit + (predictAllBound κ rows width +
    (predictAllBound κ metaCount.word.toNat width + metaCount.word.toNat * κ .visit +
      (rows * (κ .visit + κ .read) + κ .serve)))

theorem serveRun_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (serveRun κ state features).work ≤
      serveBound κ interface.actions.word.toNat features.indices.length := by
  unfold serveRun
  split
  · rename_i committed _
    split
    · exact Nat.zero_le _
    · rename_i action _ _
      exact Costed.bind_work_le (Costed.ite_work_bound _ (Nat.le_refl _) (Nat.zero_le _))
        fun _ => Costed.bind_work_le (predictAll_work κ _ features) fun _ =>
          Costed.bind_work_le (Costed.ite_work_bound _
            (Nat.le_trans (predictAll_work κ _ features) (Nat.le_add_right _ _))
            (Nat.le_add_left _ _)) fun _ =>
            Costed.bind_work_le (servedProbabilities_work κ action) fun _ => Nat.le_refl _
  · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- The costed run of `TemporalControl.choosePrimitive`: the primitive controller's rate,
its snapshot and the persistent draw. -/
def choosePrimitiveRun (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) : Costed Unit := do
  let rate ← controlRate κ state
  let snapshot ← Twin.snapshot (count := interface.actions) κ
    state.runtime.lifecycle.consumers.control features rate
  Costed.discard (drawPersistent κ snapshot state.runtime.references.rng)
  Costed.op (κ .choosePrimitive) ()

/-- Bound of a primitive draw over `width` features. -/
abbrev primitiveBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  metaRateBound κ rows capacity + (predictAllBound κ rows width + κ .snapshot +
    (persistentBound κ rows + κ .choosePrimitive))

theorem choosePrimitiveRun_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (choosePrimitiveRun κ state features).work ≤
      primitiveBound κ interface.actions.word.toNat dimension.capacity features.indices.length :=
  Costed.bind_work_le (controlRate_work κ state) fun rate =>
    Costed.bind_work_le (snapshot_work κ _ features rate) fun snapshot =>
      Costed.bind_work_le (drawPersistent_work κ snapshot _) fun _ => Nat.le_refl _

/-- The costed run of `TemporalControl.refreshFree`: the refresh of the free dispatch. -/
def refreshFreeRun (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))) : Costed Unit :=
  let free : FreeDispatch interface.symbols interface.actions config criterion dimension
      interface.signals (EndingPayload (profile.mode != .frozen)) :=
    ⟨state.runtime.lifecycle, state.runtime.references.modelPredictions, closing⟩
  Costed.charge (κ .refreshFree) (Costed.discard (refreshModels κ free profile.ranksSubtasks))

/-- Bound of a free dispatch's refresh. -/
abbrev refreshFreeBound (κ : Costs) (rows capacity positions questions units : Nat) : Nat :=
  κ .refreshFree + refreshBound κ rows capacity positions questions units

theorem refreshFreeRun_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))) :
    (refreshFreeRun κ state closing).work ≤
      refreshFreeBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity (interface.signals.length + 1) config.units.count :=
  Costed.charge_work_le (Costed.discard_work_le (refreshModels_work κ _ _))

/-- The costed run of `TemporalControl.planFree` with the planning boundary of a selection:
a frozen agent clears its errors; any other plans at the meta-controller's rate. -/
def planFreeRun (κ : Costs) (selection : PlanningSelection)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) : Costed Unit :=
  let planning : PlanningResult criterion dimension :=
    ⟨state.runtime.lifecycle.consumers.metaController, state.runtime.references.modelPredictions,
      state.runtime.references.planningSteps, state.runtime.references.planningErrors,
      state.runtime.references.recent⟩
  Costed.charge (κ .planFree) (Costed.ite ((profile.mode == .frozen) = true)
    (Costed.discard (Costed.replicate (κ .visit) Acorn.FeatureConstants.skillCount Binary32.zero))
    (do
      let rate ← metaRate κ state
      Costed.discard (Twin.planningBoundary κ selection planning
        state.runtime.lifecycle.consumers.skills features state.average.rate rate)))

/-- Bound of a free boundary's planning over `width` features. -/
abbrev planFreeBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  κ .planFree + (Acorn.FeatureConstants.skillCount * κ .visit +
    (metaRateBound κ rows capacity + planningBound κ capacity positions width))

theorem planFreeRun_work (κ : Costs) (selection : PlanningSelection)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (planFreeRun κ selection state features).work ≤
      planFreeBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length :=
  Costed.charge_work_le (Costed.ite_work_bound _ (Nat.le_add_right _ _)
    (Nat.le_trans (Costed.bind_work_le (metaRate_work κ state) fun _ =>
      Costed.discard_work_le (planningBoundary_work κ selection _ _ features _ _))
      (Nat.le_add_left _ _)))

/-- The costed run of `TemporalControl.drawMeta`: the meta-controller's rate, its snapshot
and the draw. -/
def drawMetaRun (κ : Costs) (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) : Costed Unit := do
  let rate ← metaRate κ state
  let snapshot ← Twin.snapshot (count := metaCount) κ
    state.runtime.lifecycle.consumers.metaController features rate
  Costed.discard (draw κ snapshot state.runtime.references.rng)
  Costed.op (κ .drawMeta) ()

/-- Bound of a meta draw over `width` features. -/
abbrev drawMetaBound (κ : Costs) (rows capacity width : Nat) : Nat :=
  metaRateBound κ rows capacity + (predictAllBound κ metaCount.word.toNat width + κ .snapshot +
    (κ .drawClose + max (κ .uniform) (greedyBound κ metaCount.word.toNat) + κ .drawMeta))

theorem drawMetaRun_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (drawMetaRun κ state features).work ≤
      drawMetaBound κ interface.actions.word.toNat dimension.capacity features.indices.length :=
  Costed.bind_work_le (metaRate_work κ state) fun rate =>
    Costed.bind_work_le (snapshot_work κ _ features rate) fun snapshot =>
      Costed.bind_work_le (draw_work κ snapshot _) fun _ => Nat.le_refl _

/-- A started option's continuation holds the start frame. -/
theorem beginTemporal_frame {actions : Word.Count} {discounts : List Discount}
    (skill : Skill actions config criterion dimension discounts)
    (models : OptionModelOps criterion dimension) (features : SwiftTd.ActiveSet dimension)
    (potential : Potential) (learning : Bool) (rate : ConsumerRate) :
    (skill.beginTemporal models features potential learning rate).2.2.features = features := by
  cases learning <;> rfl

/-- The start twin's continuation holds the start frame. -/
theorem beginTemporal_twin_frame {actions : Word.Count} {discounts : List Discount} (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (beginTemporal κ skill features potential learning rate).val.2.2.features = features :=
  beginTemporal_frame skill _ features potential learning rate

/-- The costed run of `TemporalControl.closeOption` with the model operations of selection:
the current owner's end, which a detached old owner does not take. -/
def closeOptionRun (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) : Costed Unit :=
  Costed.charge (κ .closeOption) (match closing.oldOwner with
    | some _ => Costed.pure ()
    | none => do
      let value ← valueFunction κ state
      Costed.discard (endTemporal κ (state.runtime.lifecycle.consumers.skills.get closing.slot)
        value features closing.activation reward terminal state.average.rate))

/-- Bound of an option's closing over `width` features. -/
abbrev closeOptionBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  κ .closeOption +
    (metaRateBound κ rows capacity + endTemporalBound κ rows capacity positions width)

theorem closeOptionRun_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension)
    (closing : Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))
    (reward terminal : Binary32) :
    (closeOptionRun κ state features closing reward terminal).work ≤
      closeOptionBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length := by
  unfold closeOptionRun
  refine Costed.charge_work_le ?_
  split
  · exact Nat.zero_le _
  · exact Costed.bind_work_le (valueFunction_work κ state) fun value =>
      Costed.discard_work_le (endTemporal_work κ _ value features _ _ _ _)

/-- The costed run of `TemporalControl.learnMeta`: the meta-controller's credit of the owed
span. -/
def learnMetaRun (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) : Costed Unit :=
  let owed := state.gap.close
  Costed.charge (κ .learnMeta) (Costed.ite ((profile.mode == .frozen) = true) (Costed.pure ())
    (Costed.discard (policyStep κ state.runtime.lifecycle.consumers.metaController features decision
      (criterion.center owed.1 owed.2 state.average.rate) owed.2)))

/-- Bound of the meta-controller's credit over `width` features. -/
abbrev learnMetaBound (κ : Costs) (capacity width : Nat) : Nat :=
  κ .learnMeta + policyStepBound κ metaCount.word.toNat capacity width

theorem learnMetaRun_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    (learnMetaRun κ state features decision).work ≤
      learnMetaBound κ dimension.capacity features.indices.length :=
  Costed.charge_work_le (Costed.ite_work_bound _ (Nat.zero_le _)
    (Costed.discard_work_le (policyStep_work κ _ features decision _ _)))

/-- The costed run of `TemporalControl.stepOption` with the model operations of selection. -/
def stepOptionRun (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32) :
    Costed Unit :=
  Costed.charge (κ .stepOption) (Costed.discard
    (stepTemporal κ (state.runtime.lifecycle.consumers.skills.get slot) activation next reward
      state.average.rate state.runtime.references.rng))

/-- Bound of an option step over `width` features. -/
abbrev stepOptionBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  κ .stepOption + stepTemporalBound κ rows capacity positions width

theorem stepOptionRun_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32) :
    (stepOptionRun κ state slot activation next reward).work ≤
      stepOptionBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity next.features.indices.length :=
  Costed.charge_work_le (Costed.discard_work_le (stepTemporal_work κ _ activation next _ _ _))

/-- The costed run of `TemporalControl.dispatchMeta` with the model operations of selection,
in the listed composition of `TemporalControl.dispatchMeta_eq`: the meta credit, then the
primitive draw or the drawn option's potential, settlement, start and first step. -/
def dispatchMetaRun (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (decision : PolicyDecision metaCount) : Costed Unit := do
  learnMetaRun κ state features decision
  let state := state.learnMeta features decision
  Costed.charge (κ .dispatchMeta) (match skillOfMeta decision.action with
    | none => choosePrimitiveRun κ state features
    | some slot =>
      let skill := state.runtime.lifecycle.consumers.skills.get slot
      Costed.bind (interestPotential κ skill.interest features declared) fun potential? =>
        match potential? with
        | none => Costed.pure ()
        | some potential => do
          let value ← valueFunction κ state
          let source ← skillSource κ state
          let estimate ← comparisonValue κ criterion decision.snapshot
          let settled ← settleTemporal κ skill value features potential goal estimate source
            reward state.average.rate (profile.mode != .frozen)
          let begun ← beginTemporal κ settled features potential (profile.mode != .frozen) source
          stepOptionRun κ (state.withSkill slot begun.1) slot begun.2.1 begun.2.2 reward)

/-- Bound of a meta dispatch over `width` features. -/
abbrev dispatchBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  learnMetaBound κ capacity width + (κ .dispatchMeta + (primitiveBound κ rows capacity width +
    (potentialBound κ width + (metaRateBound κ rows capacity + (metaRateBound κ rows capacity +
      (comparisonBound κ metaCount.word.toNat + (settleBound κ rows capacity positions width +
        (beginTemporalBound κ rows capacity positions width +
          stepOptionBound κ rows capacity positions width))))))))

theorem dispatchMetaRun_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) (decision : PolicyDecision metaCount) :
    (dispatchMetaRun κ state features declared reward goal decision).work ≤
      dispatchBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length := by
  unfold dispatchMetaRun
  refine Costed.bind_work_le (learnMetaRun_work κ state features decision) fun _ =>
    Costed.charge_work_le ?_
  split
  · exact Nat.le_trans (choosePrimitiveRun_work κ _ features) (Nat.le_add_right _ _)
  · rename_i slot _
    refine Nat.le_trans (Costed.bind_work_le (interestPotential_work κ _ features declared)
      (b := metaRateBound κ interface.actions.word.toNat dimension.capacity +
        (metaRateBound κ interface.actions.word.toNat dimension.capacity +
          (comparisonBound κ metaCount.word.toNat +
            (settleBound κ interface.actions.word.toNat dimension.capacity
              (rankDimension dimension).capacity features.indices.length +
              (beginTemporalBound κ interface.actions.word.toNat dimension.capacity
                (rankDimension dimension).capacity features.indices.length +
                stepOptionBound κ interface.actions.word.toNat dimension.capacity
                  (rankDimension dimension).capacity features.indices.length)))))
      fun potential? => ?_) ?_
    · cases potential? with
      | none => exact Nat.zero_le _
      | some potential =>
        exact Costed.bind_work_le (valueFunction_work κ _) fun value =>
          Costed.bind_work_le (skillSource_work κ _) fun source =>
            Costed.bind_work_le (comparisonValue_work κ criterion _) fun estimate =>
              Costed.bind_work_le (settleTemporal_work κ _ value features potential goal estimate
                source reward _ _) fun settled =>
                Costed.bind_work_le_at (beginTemporal_work κ settled features potential _ source)
                  (Nat.le_trans (stepOptionRun_work κ _ slot _ _ reward)
                    (Nat.le_of_eq (by rw [beginTemporal_twin_frame])))
    · omega

/-- The costed run of `TemporalControl.atBoundary` with the model operations and planning
boundary of selection: the refresh, the planning, the meta draw, the closing of an ending
option, and the dispatch. -/
def atBoundaryRun (κ : Costs) (selection : PlanningSelection)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))) : Costed Unit := do
  refreshFreeRun κ state closing
  let refreshed := state.refreshFree closing
  planFreeRun κ selection refreshed.1 features
  let planned := refreshed.1.planFree (Features.planningBoundary selection) features
  drawMetaRun κ planned features
  let drawn := planned.drawMeta features
  Costed.charge (κ .atBoundary) (match refreshed.2 with
    | none => dispatchMetaRun κ drawn.1 features declared reward goal drawn.2
    | some closing => do
      closeOptionRun κ drawn.1 features closing reward drawn.2.continuation
      let result := drawn.1.closeOption (modelOperations criterion dimension) features closing
        reward drawn.2.continuation
      dispatchMetaRun κ result.1 features declared reward goal drawn.2)

/-- Bound of a free dispatch over `width` features. -/
abbrev atBoundaryBound (κ : Costs) (rows capacity positions questions units width : Nat) : Nat :=
  refreshFreeBound κ rows capacity positions questions units +
    (planFreeBound κ rows capacity positions width + (drawMetaBound κ rows capacity width +
      (κ .atBoundary + (closeOptionBound κ rows capacity positions width +
        dispatchBound κ rows capacity positions width))))

theorem atBoundaryRun_work (κ : Costs) (selection : PlanningSelection)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))) :
    (atBoundaryRun κ selection state features declared reward goal closing).work ≤
      atBoundaryBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity (interface.signals.length + 1) config.units.count
        features.indices.length := by
  unfold atBoundaryRun
  refine Costed.bind_work_le (refreshFreeRun_work κ state closing) fun _ =>
    Costed.bind_work_le (planFreeRun_work κ selection _ features) fun _ =>
      Costed.bind_work_le (drawMetaRun_work κ _ features) fun _ => Costed.charge_work_le ?_
  split
  · exact Nat.le_trans (dispatchMetaRun_work κ _ features declared reward goal _)
      (Nat.le_add_left _ _)
  · exact Costed.bind_work_le (closeOptionRun_work κ _ features _ reward _) fun _ =>
      dispatchMetaRun_work κ _ features declared reward goal _

/-- The costed run of `TemporalControl.select` at a planning selection: the preparation, a
served step, a primitive-only draw, a free dispatch, or an executing option's decision and
its step or its closing. -/
def selectRun (κ : Costs) (selection : PlanningSelection)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) : Costed Unit := do
  prepareRun κ state features reward
  let state := state.prepareSelection (modelOperations criterion dimension) features reward
  serveRun κ state features
  Costed.charge (κ .select) (match state.serve features with
    | some _ => Costed.pure ()
    | none => Costed.ite ((!profile.usesHierarchy) = true)
        (do
          Costed.discard (Costed.replicate (κ .visit) metaCount.word.toNat Binary32.zero)
          choosePrimitiveRun κ (state.withPhase .idle) features)
        (let phase := state.runtime.references.phase
          let state := state.withPhase .idle
          match phase with
          | .idle | .exploring _ =>
            atBoundaryRun κ selection state features declared reward goal none
          | .option slot activation =>
            let skill := state.runtime.lifecycle.consumers.skills.get slot
            Costed.bind (interestPotential κ skill.interest features declared) fun potential? =>
              match potential? with
              | none => Costed.pure ()
              | some potential => do
                let rate ← metaRate κ state
                let metaPolicy ← Twin.snapshot (count := metaCount) κ
                  state.runtime.lifecycle.consumers.metaController features rate
                let estimate ← comparisonValue κ criterion metaPolicy
                let source ← skillSource κ state
                Costed.bind
                  (decideOption κ skill activation features potential goal estimate source)
                  fun decision =>
                    match decision with
                    | .continuing next => do
                      Costed.discard (Costed.replicate (κ .visit)
                        Acorn.FeatureConstants.skillCount Binary32.zero)
                      stepOptionRun κ state.withoutPlanning slot activation next reward
                    | .ending reason =>
                      let closing : Closing interface.actions config criterion dimension
                          interface.layout (EndingPayload (profile.mode != .frozen)) :=
                        ⟨slot, ⟨activation, potential, reason⟩, none⟩
                      Costed.ite (criterion = .differential)
                        (atBoundaryRun κ selection state features declared reward goal
                          (some closing))
                        (do
                          closeOptionRun κ state features closing reward estimate
                          let result := state.closeOption (modelOperations criterion dimension)
                            features closing reward estimate
                          atBoundaryRun κ selection result.1 features declared reward goal none)))

/-- Bound of an executing option's decision and its step or closing over `width` features. -/
abbrev optionBranchBound (κ : Costs) (rows capacity positions questions units width : Nat) :
    Nat :=
  potentialBound κ width + (metaRateBound κ rows capacity +
    (predictAllBound κ metaCount.word.toNat width + κ .snapshot +
      (comparisonBound κ metaCount.word.toNat + (metaRateBound κ rows capacity +
        (decideBound κ rows capacity width +
          (Acorn.FeatureConstants.skillCount * κ .visit +
            stepOptionBound κ rows capacity positions width +
            (closeOptionBound κ rows capacity positions width +
              atBoundaryBound κ rows capacity positions questions units width)))))))

/-- Bound of selection over `width` features. -/
abbrev selectBound (κ : Costs) (rows capacity positions questions units width : Nat) : Nat :=
  prepareBound κ rows capacity positions width + (serveBound κ rows width + (κ .select +
    (metaCount.word.toNat * κ .visit + primitiveBound κ rows capacity width +
      (atBoundaryBound κ rows capacity positions questions units width +
        optionBranchBound κ rows capacity positions questions units width))))

theorem selectRun_work (κ : Costs) (selection : PlanningSelection)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) :
    (selectRun κ selection state features declared reward goal).work ≤
      selectBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity (interface.signals.length + 1) config.units.count
        features.indices.length := by
  unfold selectRun
  refine Costed.bind_work_le (prepareRun_work κ state features reward) fun _ =>
    Costed.bind_work_le (serveRun_work κ _ features) fun _ => Costed.charge_work_le ?_
  split
  · exact Nat.zero_le _
  · refine Costed.ite_work_bound _ ?_ ?_
    · exact Nat.le_trans (Costed.bind_work_le (Nat.le_refl _) fun _ =>
        choosePrimitiveRun_work κ _ features) (Nat.le_add_right _ _)
    · refine Nat.le_trans ?_ (Nat.le_add_left _ _)
      dsimp only
      split
      · exact Nat.le_trans (atBoundaryRun_work κ selection _ features declared reward goal none)
          (Nat.le_add_right _ _)
      · exact Nat.le_trans (atBoundaryRun_work κ selection _ features declared reward goal none)
          (Nat.le_add_right _ _)
      · rename_i slot activation _
        refine Nat.le_trans ?_ (Nat.le_add_left _ _)
        refine Costed.bind_work_le (interestPotential_work κ _ features declared)
          fun potential? => ?_
        cases potential? with
        | none => exact Nat.zero_le _
        | some potential =>
          refine Costed.bind_work_le (metaRate_work κ _) fun rate =>
            Costed.bind_work_le (snapshot_work κ _ features rate) fun metaPolicy =>
              Costed.bind_work_le (comparisonValue_work κ criterion metaPolicy) fun estimate =>
                Costed.bind_work_le (skillSource_work κ _) fun source =>
                  Costed.bind_work_le_at
                    (decideOption_work κ _ activation features potential goal estimate source) ?_
          split
          · rename_i next continuing
            have frame := (Skill.decide_frame _ activation features potential goal estimate
              source next continuing).1
            exact Nat.le_trans (Costed.bind_work_le (Nat.le_refl _)
              (b := stepOptionBound κ interface.actions.word.toNat dimension.capacity
                (rankDimension dimension).capacity features.indices.length) fun _ =>
              Nat.le_trans (stepOptionRun_work κ _ slot activation next reward)
                (Nat.le_of_eq (by rw [frame]))) (Nat.le_add_right _ _)
          · refine Nat.le_trans (Costed.ite_work_bound _
              (bound := closeOptionBound κ interface.actions.word.toNat dimension.capacity
                  (rankDimension dimension).capacity features.indices.length +
                atBoundaryBound κ interface.actions.word.toNat dimension.capacity
                  (rankDimension dimension).capacity (interface.signals.length + 1)
                  config.units.count features.indices.length) ?_ ?_) (Nat.le_add_left _ _)
            · exact Nat.le_trans (atBoundaryRun_work κ selection _ features declared reward goal _)
                (Nat.le_add_left _ _)
            · exact Costed.bind_work_le (closeOptionRun_work κ _ features _ reward estimate)
                fun _ => atBoundaryRun_work κ selection _ features declared reward goal none

/-- Twin of `TemporalControl.alignedSelect`: selection's value with its proof, and the work
of its run. -/
def alignedSelect (κ : Costs) (state : TemporalControl interface profile config criterion dimension)
    (aligned : state.Aligned) (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (observation : Frame interface) (reward : Binary32)
    (goal : Bool) :
    Costed { result : TemporalControl interface profile config criterion dimension ×
        TemporalDecision interface.actions //
      state.select planning features observation.declared reward goal = some result } :=
  Costed.via (state.alignedSelect aligned planning features observation reward goal)
    (selectRun κ planning state features observation.declared reward goal)

end AcornVerif.Resource.Twin
