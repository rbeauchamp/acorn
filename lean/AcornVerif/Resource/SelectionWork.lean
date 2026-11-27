import Acorn.Handcrafted.StepParts
import AcornVerif.Resource.EncodeWork
import AcornVerif.Resource.PlanWork
import AcornVerif.Resource.RefreshWork

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension}

def rateRun {policy : RatePolicy} (rate : RateState policy)
    (own primitive annealed : Costed Unit) : Costed Unit :=
  match rate with
  | .declared => Costed.pure ()
  | .perLearner => own
  | .shared => primitive
  | .annealed _ => annealed

theorem rateRun_work {policy : RatePolicy} (rate : RateState policy)
    (own primitive annealed : Costed Unit) (bound : Nat) (ownFits : own.work ≤ bound)
    (primitiveFits : primitive.work ≤ bound) (annealedFits : annealed.work ≤ bound) :
    (rateRun rate own primitive annealed).work ≤ bound := by
  cases rate
  · exact Nat.zero_le _
  · exact ownFits
  · exact primitiveFits
  · exact annealedFits

def primitiveRate (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    Costed SwiftTd.ExploreRate :=
  exploreRate (count := interface.actions) κ state.runtime.lifecycle.consumers.control

theorem primitiveRate_costed (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    state.primitiveRateCosted.Within κ (primitiveRate κ state).work :=
  primitiveRateCosted_within κ state

def metaRate (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    Costed SwiftTd.ExploreRate :=
  ⟨state.metaRate, metaRateBound κ interface.actions.word.toNat dimension.capacity⟩

theorem metaRate_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    (metaRate κ state).work ≤ metaRateBound κ interface.actions.word.toNat dimension.capacity :=
  Nat.le_refl _

theorem metaRate_costed (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    state.metaRateCosted.Within κ (metaRate κ state).work := metaRateCosted_within κ state

def controlRate (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    Costed SwiftTd.ExploreRate :=
  Costed.via state.controlRate (rateRun state.rate (Costed.discard (primitiveRate κ state))
    (Costed.discard (primitiveRate κ state)) (Costed.op (κ .rateClose) ()))

theorem controlRate_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    (controlRate κ state).work ≤ metaRateBound κ interface.actions.word.toNat dimension.capacity :=
  rateRun_work _ _ _ _ _
    (Nat.le_trans (exploreRate_work (count := interface.actions) κ
      state.runtime.lifecycle.consumers.control) (Nat.le_add_left _ _))
    (Nat.le_trans (exploreRate_work (count := interface.actions) κ
      state.runtime.lifecycle.consumers.control) (Nat.le_add_left _ _))
    (by change κ .rateClose ≤ _; simp only [metaRateBound, rateBound]; omega)

def skillSource (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    Costed ConsumerRate :=
  ⟨state.skillRate, rateBound κ interface.actions.word.toNat dimension.capacity⟩

theorem skillSource_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    (skillSource κ state).work ≤ metaRateBound κ interface.actions.word.toNat dimension.capacity :=
  Nat.le_add_left _ _

theorem skillSource_costed (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    state.skillRateCosted.Within κ (skillSource κ state).work := skillSourceCosted_within κ state

def valueFunction (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    Costed (ValueFunction criterion dimension) :=
  ⟨state.valueFunction, metaRateBound κ interface.actions.word.toNat dimension.capacity⟩

theorem valueFunction_val (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    (valueFunction κ state).val = state.valueFunction := rfl

theorem valueFunction_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    (valueFunction κ state).work ≤
      metaRateBound κ interface.actions.word.toNat dimension.capacity :=
  Nat.le_refl _

theorem valueFunction_costed (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension) :
    state.valueFunctionCosted.Within κ (valueFunction κ state).work :=
  valueFunctionCosted_within κ state

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

abbrev prepareBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  κ .prepare + Library.vectorMap.work (κ .visit) Acorn.FeatureConstants.skillCount
    (metaRateBound κ rows capacity +
    (predictBound κ positions width + κ .read))

theorem prepareRun_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (reward : Binary32) :
    (prepareRun κ state features reward).work ≤
      prepareBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length :=
  Costed.charge_work_le (Costed.ite_work_bound _ (Costed.discard_work_le
    (Costed.mapVector_work_le _ _ _ _ fun skill _ =>
      Costed.bind_work_le (valueFunction_work κ _) fun value =>
        Costed.bind_work_le (predict_work κ skill.model value features ⟨0, by decide⟩) fun _ =>
          Nat.le_refl _)) (Nat.zero_le _))

def serveRun (κ : Costs) (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) : Costed Unit :=
  match state.runtime.references.phase with
  | .exploring committed =>
    match committed.run.serve with
    | none => Costed.pure ()
    | some (action, _) => do
      Costed.discard (predictAll κ state.runtime.lifecycle.consumers.control features)
      Costed.ite (profile.usesHierarchy = true)
        (Costed.discard (predictAll κ state.runtime.lifecycle.consumers.metaController features))
        (Costed.pure ())
      Costed.discard (servedProbabilities κ action)
      Costed.op (κ .serve) ()
  | .idle | .option _ _ => Costed.pure ()

abbrev serveBound (κ : Costs) (rows width : Nat) : Nat :=
  predictAllBound κ rows width +
    (predictAllBound κ metaCount.word.toNat width +
      (Library.ofFn.work (κ .visit) rows (κ .read) + κ .serve))

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
      exact Costed.bind_work_le
        (predictAll_work κ state.runtime.lifecycle.consumers.control features) fun _ =>
        Costed.bind_work_le (Costed.ite_work_bound _
          (predictAll_work κ state.runtime.lifecycle.consumers.metaController features)
          (Nat.zero_le _)) fun _ =>
          Costed.bind_work_le (servedProbabilities_work κ action) fun _ => Nat.le_refl _
  · exact Nat.zero_le _
  · exact Nat.zero_le _

def choosePrimitiveRun (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) : Costed Unit := do
  let rate ← controlRate κ state
  let snapshot ← Twin.snapshot (count := interface.actions) κ
    state.runtime.lifecycle.consumers.control features rate
  Costed.discard (drawPersistent κ snapshot state.runtime.references.rng)
  Costed.op (κ .choosePrimitive) ()

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
      Costed.bind_work_le (drawPersistent_work κ snapshot state.runtime.references.rng)
        fun _ => Nat.le_refl _

def refreshFreeRun (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))) : Costed Unit :=
  let free : FreeDispatch interface.symbols interface.actions config criterion dimension
      interface.signals (EndingPayload (profile.mode != .frozen)) :=
    ⟨state.runtime.lifecycle, state.runtime.references.modelPredictions, closing⟩
  Costed.charge (κ .refreshFree) (Costed.discard (refreshModels κ free profile.ranksSubtasks))

abbrev refreshFreeBound (κ : Costs) (rows capacity positions units : Nat) : Nat :=
  κ .refreshFree + refreshBound κ rows capacity positions units

theorem refreshFreeRun_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (closing : Option (Closing interface.actions config criterion dimension interface.layout
      (EndingPayload (profile.mode != .frozen)))) :
    (refreshFreeRun κ state closing).work ≤
      refreshFreeBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity config.units.count :=
  Costed.charge_work_le (Costed.discard_work_le (refreshModels_work κ _ _))

def planFreeRun (κ : Costs) (selection : PlanningSelection)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) : Costed Unit :=
  let planning : PlanningResult criterion dimension :=
    ⟨state.runtime.lifecycle.consumers.metaController, state.runtime.references.modelPredictions,
      state.runtime.references.planningSteps, state.runtime.references.planningErrors,
      state.runtime.references.recent⟩
  Costed.charge (κ .planFree) (Costed.ite ((profile.mode == .frozen) = true)
    (Costed.pure ())
    (do
      let rate ← metaRate κ state
      Costed.discard (Twin.planningBoundary κ selection planning
        state.runtime.lifecycle.consumers.skills features state.average.rate rate)))

abbrev planFreeBound (κ : Costs) (rows capacity positions width : Nat) : Nat :=
  κ .planFree + (metaRateBound κ rows capacity + planningBound κ capacity positions width)

theorem planFreeRun_work (κ : Costs) (selection : PlanningSelection)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) :
    (planFreeRun κ selection state features).work ≤
      planFreeBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity features.indices.length :=
  Costed.charge_work_le (Costed.ite_work_bound _ (Nat.zero_le _)
    (Costed.bind_work_le (metaRate_work κ state) fun _ =>
      Costed.discard_work_le (planningBoundary_work κ selection _ _ features _ _)))

def drawMetaRun (κ : Costs) (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) : Costed Unit := do
  let rate ← metaRate κ state
  let snapshot ← Twin.snapshot (count := metaCount) κ
    state.runtime.lifecycle.consumers.metaController features rate
  Costed.discard (draw κ snapshot state.runtime.references.rng)
  Costed.op (κ .drawMeta) ()

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
      Costed.bind_work_le (draw_work κ snapshot state.runtime.references.rng) fun _ =>
        Nat.le_refl _

theorem beginTemporal_twin_frame {actions : Word.Count} {discounts : List Discount} (κ : Costs)
    (skill : Skill actions config criterion dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (potential : Potential) (learning : Bool)
    (rate : ConsumerRate) :
    (beginTemporal κ skill features potential learning rate).val.2.2.features = features :=
  beginTemporal_frame skill _ features potential learning rate

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

def learnMetaRun (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) : Costed Unit :=
  let owed := state.gap.close
  Costed.charge (κ .learnMeta) (Costed.ite ((profile.mode == .frozen) = true) (Costed.pure ())
    (Costed.discard (policyStep κ state.runtime.lifecycle.consumers.metaController features decision
      (criterion.center owed.1 owed.2 state.average.rate) owed.2)))

abbrev learnMetaBound (κ : Costs) (capacity width : Nat) : Nat :=
  κ .learnMeta + policyStepBound κ metaCount.word.toNat capacity width

theorem learnMetaRun_work (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision metaCount) :
    (learnMetaRun κ state features decision).work ≤
      learnMetaBound κ dimension.capacity features.indices.length :=
  Costed.charge_work_le (Costed.ite_work_bound _ (Nat.zero_le _)
    (Costed.discard_work_le (policyStep_work κ _ features decision _ _)))

def stepOptionRun (κ : Costs)
    (state : TemporalControl interface profile config criterion dimension)
    (slot : Fin Acorn.FeatureConstants.skillCount)
    (activation : OptionActivation (profile.mode != .frozen))
    (next : OptionContinuation interface.actions dimension activation) (reward : Binary32) :
    Costed Unit :=
  Costed.charge (κ .stepOption) (Costed.discard
    (stepTemporal κ (state.runtime.lifecycle.consumers.skills.get slot) activation next reward
      state.average.rate state.runtime.references.rng))

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
            Costed.bind_work_le (comparisonValue_work κ criterion decision.snapshot)
              fun estimate =>
              Costed.bind_work_le (settleTemporal_work κ _ value features potential goal estimate
                source reward _ _) fun settled =>
                Costed.bind_work_le_at (beginTemporal_work κ settled features potential _ source)
                  (Nat.le_trans (stepOptionRun_work κ _ slot _ _ reward)
                    (Nat.le_of_eq (by rw [beginTemporal_twin_frame])))
    · omega

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

abbrev atBoundaryBound (κ : Costs) (rows capacity positions units width : Nat) : Nat :=
  refreshFreeBound κ rows capacity positions units +
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
        (rankDimension dimension).capacity config.units.count
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
        (choosePrimitiveRun κ (state.withPhase .idle) features)
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
                    | .continuing next =>
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

abbrev optionBranchBound (κ : Costs) (rows capacity positions units width : Nat) :
    Nat :=
  potentialBound κ width + (metaRateBound κ rows capacity +
    (predictAllBound κ metaCount.word.toNat width + κ .snapshot +
      (comparisonBound κ metaCount.word.toNat + (metaRateBound κ rows capacity +
        (decideBound κ rows capacity width +
          (stepOptionBound κ rows capacity positions width +
            (closeOptionBound κ rows capacity positions width +
              atBoundaryBound κ rows capacity positions units width)))))))

abbrev selectBound (κ : Costs) (rows capacity positions units width : Nat) : Nat :=
  prepareBound κ rows capacity positions width + (serveBound κ rows width + (κ .select +
    (primitiveBound κ rows capacity width +
      (atBoundaryBound κ rows capacity positions units width +
        optionBranchBound κ rows capacity positions units width))))

theorem selectRun_work (κ : Costs) (selection : PlanningSelection)
    (state : TemporalControl interface profile config criterion dimension)
    (features : SwiftTd.ActiveSet dimension) (declared : DeclaredPotentials) (reward : Binary32)
    (goal : Bool) :
    (selectRun κ selection state features declared reward goal).work ≤
      selectBound κ interface.actions.word.toNat dimension.capacity
        (rankDimension dimension).capacity config.units.count
        features.indices.length := by
  unfold selectRun
  refine Costed.bind_work_le (prepareRun_work κ state features reward) fun _ =>
    Costed.bind_work_le (serveRun_work κ _ features) fun _ => Costed.charge_work_le ?_
  split
  · exact Nat.zero_le _
  · refine Costed.ite_work_bound _ ?_ ?_
    · exact Nat.le_trans (choosePrimitiveRun_work κ _ features) (Nat.le_add_right _ _)
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
            refine Nat.le_trans (stepOptionRun_work κ _ slot activation next reward)
              (Nat.le_trans (Nat.le_of_eq ?_) (Nat.le_add_right
                (stepOptionBound κ interface.actions.word.toNat dimension.capacity
                  (rankDimension dimension).capacity features.indices.length) _))
            rw [frame]
          · refine Nat.le_trans (Costed.ite_work_bound _
              (bound := closeOptionBound κ interface.actions.word.toNat dimension.capacity
                  (rankDimension dimension).capacity features.indices.length +
                atBoundaryBound κ interface.actions.word.toNat dimension.capacity
                  (rankDimension dimension).capacity
                  config.units.count features.indices.length) ?_ ?_) (Nat.le_add_left _ _)
            · exact Nat.le_trans (atBoundaryRun_work κ selection _ features declared reward goal _)
                (Nat.le_add_left _ _)
            · exact Costed.bind_work_le (closeOptionRun_work κ _ features _ reward estimate)
                fun _ => atBoundaryRun_work κ selection _ features declared reward goal none

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
