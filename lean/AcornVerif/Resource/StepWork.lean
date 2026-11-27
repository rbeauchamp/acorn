import Mathlib.Tactic.GCongr
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Nat
import AcornVerif.Resource.SelectionWork

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

def chooseRun (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) : Costed Unit := do
  Costed.op (κ .choose) ()
  let prepared := state.advanceClock
  Costed.discard (frame κ prepared percept.frame)
  selectRun κ (firstPlanning order planning) prepared.control
    (prepared.frame percept.frame).active percept.frame.declared percept.reward
    percept.frame.achieved

def chooseSelected (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (selects : order ≠ .actThenLearn) (percept : Percept interface) :
    Costed (Chosen interface profile config criterion dimension planning) :=
  Costed.via (state.chooseSelected order selects percept) (chooseRun κ state order percept)

abbrev frameWidth (interface : Interface) (config : Features.Config) : Nat :=
  config.tilings.toNat * (interface.words + interface.layout.length) + config.units.count

theorem selectBound_mono (κ : Costs) (rows capacity positions units : Nat)
    {width limit : Nat} (fits : width ≤ limit) :
    selectBound κ rows capacity positions units width ≤
      selectBound κ rows capacity positions units limit := by
  simp only [selectBound, prepareBound, serveBound, primitiveBound, atBoundaryBound,
    optionBranchBound, planFreeBound, drawMetaBound, closeOptionBound, dispatchBound,
    planningBound, backupAllBound, backupErrorBound, lookAheadBound, predictBound, inputBound,
    lookaheadBound, outcomeValuesBound, rowInputBound, expectedAtBound, planBound, predictAllBound,
    potentialBound, decideBound, frozenBound, stepOptionBound, stepTemporalBound, optionStepBound,
    policyStepBound, creditStepBound, secondLoopBound, modelStepBound, transitionStepBound,
    stepBound, updateRowsBound, endTemporalBound, modelTerminalWorkBound, outcomeBound,
    indicatorBound, settleBound, stopFollowingBound, modelStopBound, beginTemporalBound,
    beginOptionBound, modelBeginBound, transitionBeginBound, beginBound, learnMetaBound, pass,
    Library.work, Library.control, Library.passes]
  gcongr

abbrev chooseBound (κ : Costs) (interface : Interface) (config : Features.Config)
    (dimension : Dimension) : Nat :=
  κ .choose + (frameBound κ interface dimension.capacity config +
    selectBound κ interface.actions.word.toNat dimension.capacity
      (rankDimension dimension).capacity config.units.count
      (frameWidth interface config))

theorem chooseSelected_work (κ : Costs)
    (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (selects : order ≠ .actThenLearn) (percept : Percept interface) :
    (chooseSelected κ state order selects percept).work ≤
      chooseBound κ interface config dimension :=
  Costed.bind_work_le (Nat.le_refl _) fun _ =>
    Costed.bind_work_le (frame_work κ state.advanceClock percept.frame) fun _ =>
      Nat.le_trans (selectRun_work κ _ _ _ _ _ _)
        (selectBound_mono κ _ _ _ _ (Agent.frame_length _ percept.frame))

def SiteBounds (words κ : Costs) : Prop := ∀ site, words site ≤ κ site

private theorem add_le {a b c d : Nat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Nat.add_le_add h1 h2

private theorem frameBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (interface : Interface) (capacity : Nat) (config : Features.Config) :
    frameBound words interface capacity config ≤ frameBound κ interface capacity config := by
  simp only [frameBound, wordsBound, projectionBound, encodeBound, tiledBound, uniqueBound,
    pass, Library.work, Library.control]
  gcongr <;> exact bounds _

private theorem predictBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (positions width : Nat) :
    predictBound words positions width ≤ predictBound κ positions width := by
  simp only [predictBound, inputBound, lookaheadBound, outcomeValuesBound, comparisonBound,
    expectedBound, bestBound, rowInputBound, expectedAtBound, rankedValuesBound, occupiedBound,
    Library.work, Library.control]
  gcongr <;> exact bounds _

private theorem predictAllBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows width : Nat) : predictAllBound words rows width ≤ predictAllBound κ rows width := by
  simp only [predictAllBound, Library.work, Library.control]
  gcongr <;> exact bounds _

private theorem metaRateBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows width : Nat) : metaRateBound words rows width ≤ metaRateBound κ rows width := by
  simp only [metaRateBound, rateBound, normalizedBound, Library.work, Library.control]
  gcongr <;> exact bounds _

private theorem modelBeginBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (capacity positions width : Nat) :
    modelBeginBound words capacity positions width ≤
      modelBeginBound κ capacity positions width := by
  simp only [modelBeginBound, inputBound, beginBound, transitionBeginBound, rowInputBound,
    updateRowsBound, zeroBound, secondLoopBound, pass, Library.work, Library.control]
  gcongr <;> exact bounds _

private theorem modelStepBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (capacity positions width : Nat) :
    modelStepBound words capacity positions width ≤ modelStepBound κ capacity positions width := by
  simp only [modelStepBound, inputBound, transitionStepBound, rowInputBound, updateRowsBound,
    stepBound, firstLoopBound, secondLoopBound, pass, firstVisit, Library.work, Library.control]
  gcongr <;> exact bounds _

private theorem modelTerminalWorkBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (capacity positions width : Nat) :
    modelTerminalWorkBound words capacity positions width ≤
      modelTerminalWorkBound κ capacity positions width := by
  simp only [modelTerminalWorkBound, outcomeBound, modelTerminalBound, updateRowsBound,
    terminalBound, firstLoopBound, zeroBound, firstVisit, indicatorBound, rankedValuesBound,
    comparisonBound, expectedBound, bestBound, occupiedBound, predictAllBound, Library.work,
    Library.control]
  gcongr <;> exact bounds _

private theorem modelStopBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (capacity positions width : Nat) :
    modelStopBound words capacity positions width ≤ modelStopBound κ capacity positions width := by
  simp only [modelStopBound, outcomeBound, stopTrajectoryBound, updateRowsBound, firstLoopBound,
    releaseBound, firstVisit, indicatorBound, rankedValuesBound, comparisonBound, expectedBound,
    bestBound, occupiedBound, predictAllBound, Library.work, Library.control]
  gcongr <;> exact bounds _

private theorem optionStepBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity width : Nat) :
    optionStepBound words rows capacity width ≤ optionStepBound κ rows capacity width := by
  simp only [optionStepBound, persistentBound, policyStepBound, creditStepBound, creditBound,
    secondLoopBound, pass, firstLoopBound, zeroBound, firstVisit, greedyBound, probabilitiesBound,
    candidatesBound, bestBound, Library.work, Library.control]
  gcongr <;> exact bounds _

private theorem stepOptionBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity positions width : Nat) :
    stepOptionBound words rows capacity positions width ≤
      stepOptionBound κ rows capacity positions width :=
  add_le (bounds _) (add_le (optionStepBound_costs bounds rows capacity width)
    (modelStepBound_costs bounds capacity positions width))

private theorem closeOptionBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity positions width : Nat) :
    closeOptionBound words rows capacity positions width ≤
      closeOptionBound κ rows capacity positions width := by
  have credit : terminalCreditBound words rows capacity ≤ terminalCreditBound κ rows capacity := by
    simp only [terminalCreditBound, firstLoopBound, clearBound, zeroBound, firstVisit, Library.work,
      Library.control]
    gcongr <;> exact bounds _
  exact add_le (bounds _) (add_le (metaRateBound_costs bounds rows capacity)
    (add_le (add_le (bounds _) credit)
      (modelTerminalWorkBound_costs bounds capacity positions width)))

private theorem decideBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity width : Nat) :
    decideBound words rows capacity width ≤ decideBound κ rows capacity width := by
  simp only [decideBound, frozenBound, rateBound, normalizedBound, comparisonBound, expectedBound,
    bestBound, predictAllBound, Library.work, Library.control]
  gcongr <;> exact bounds _

private theorem settleBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity positions width : Nat) :
    settleBound words rows capacity positions width ≤
      settleBound κ rows capacity positions width := by
  have err : backupErrorBound words rows ≤ backupErrorBound κ rows := by
    simp only [backupErrorBound, expectedBound, bestBound, Library.work, Library.control]
    gcongr <;> exact bounds _
  have stopB : stopBound words rows capacity ≤ stopBound κ rows capacity := by
    simp only [stopBound, creditBound, firstLoopBound, zeroBound, firstVisit, releaseBound,
      Library.work, Library.control]
    gcongr <;> exact bounds _
  have stopF : stopFollowingBound words rows capacity positions width ≤
      stopFollowingBound κ rows capacity positions width :=
    add_le stopB (add_le (bounds _) (modelStopBound_costs bounds capacity positions width))
  exact add_le (decideBound_costs bounds rows capacity width)
    (add_le (add_le (add_le (bounds _) err)
      (add_le stopB (modelStepBound_costs bounds capacity positions width))) stopF)

private theorem planFreeBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity positions width : Nat) :
    planFreeBound words rows capacity positions width ≤
      planFreeBound κ rows capacity positions width := by
  have look : ∀ w, lookAheadBound words positions w ≤ lookAheadBound κ positions w := fun w => by
    have rest : planBound words w + words .planClose + words .lookAhead ≤
        planBound κ w + κ .planClose + κ .lookAhead := by
      simp only [planBound, pass, Library.work, Library.control]
      gcongr <;> exact bounds _
    exact add_le (predictBound_costs bounds positions w) rest
  have backup : backupAllBound words positions width ≤ backupAllBound κ positions width := by
    have h1 := look width
    unfold backupAllBound
    simp only [Library.work, Library.control]
    gcongr <;> exact bounds _
  have sweep : sweepAllBound words positions capacity ≤ sweepAllBound κ positions capacity := by
    have h2 := look capacity
    unfold sweepAllBound
    simp only [Library.work, Library.control]
    gcongr <;> exact bounds _
  exact add_le (bounds _) (add_le (metaRateBound_costs bounds rows capacity)
    (add_le (add_le backup sweep) (bounds _)))

private theorem refreshFreeBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity positions units : Nat) :
    refreshFreeBound words rows capacity positions units ≤
      refreshFreeBound κ rows capacity positions units := by
  simp only [refreshFreeBound, refreshBound, refreshRankedBound, rerankModelsBound,
    rankedSlotsBound, transitionRerankBound, rankedRerankBound, changedBound, forgetBound,
    columnsBound, learnerInitialBound, zeroBound, mergedBound, tabulateBound, candidateListBound,
    rankedBound, pass, rankedCandidatesBound, installBound, skillInitialBound,
    controllerInitialBound, modelInitialBound, transitionInitialBound, rankedEmptyBound,
    Library.work, Library.control]
  gcongr <;> exact bounds _

private theorem primitiveBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity width : Nat) :
    primitiveBound words rows capacity width ≤ primitiveBound κ rows capacity width := by
  have pers : persistentBound words rows ≤ persistentBound κ rows := by
    simp only [persistentBound, greedyBound, probabilitiesBound, candidatesBound, bestBound, pass,
      Library.work, Library.control]
    gcongr <;> exact bounds _
  exact add_le (metaRateBound_costs bounds rows capacity)
    (add_le (add_le (predictAllBound_costs bounds rows width) (bounds _))
      (add_le pers (bounds _)))

private theorem potentialBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (width : Nat) : potentialBound words width ≤ potentialBound κ width := by
  simp only [potentialBound, Library.control]
  gcongr <;> exact bounds _

private theorem comparisonBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (count : Nat) : comparisonBound words count ≤ comparisonBound κ count := by
  simp only [comparisonBound, expectedBound, bestBound, Library.work, Library.control]
  gcongr <;> exact bounds _

private theorem dispatchBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity positions width : Nat) :
    dispatchBound words rows capacity positions width ≤
      dispatchBound κ rows capacity positions width := by
  have learnM : learnMetaBound words capacity width ≤ learnMetaBound κ capacity width := by
    simp only [learnMetaBound, policyStepBound, creditStepBound, creditBound, secondLoopBound,
      pass, firstLoopBound, zeroBound, firstVisit, Library.work, Library.control]
    gcongr <;> exact bounds _
  have beginO : beginOptionBound words rows capacity width ≤
      beginOptionBound κ rows capacity width := by
    simp only [beginOptionBound, clearBound, zeroBound, frozenBound, rateBound, normalizedBound,
      predictAllBound, Library.work, Library.control]
    gcongr <;> exact bounds _
  exact add_le learnM (add_le (bounds _) (add_le (primitiveBound_costs bounds rows capacity width)
    (add_le (potentialBound_costs bounds width) (add_le (metaRateBound_costs bounds rows capacity)
      (add_le (metaRateBound_costs bounds rows capacity)
        (add_le (comparisonBound_costs bounds metaCount.word.toNat)
          (add_le (settleBound_costs bounds rows capacity positions width)
            (add_le (add_le beginO (modelBeginBound_costs bounds capacity positions width))
              (stepOptionBound_costs bounds rows capacity positions width)))))))))

private theorem atBoundaryBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity positions units width : Nat) :
    atBoundaryBound words rows capacity positions units width ≤
      atBoundaryBound κ rows capacity positions units width := by
  have drawM : drawMetaBound words rows capacity width ≤ drawMetaBound κ rows capacity width := by
    have tail : words .drawClose + max (words .uniform) (greedyBound words metaCount.word.toNat) +
        words .drawMeta ≤
        κ .drawClose + max (κ .uniform) (greedyBound κ metaCount.word.toNat) + κ .drawMeta := by
      simp only [greedyBound, candidatesBound, pass, bestBound, Library.work, Library.control]
      gcongr <;> exact bounds _
    exact add_le (metaRateBound_costs bounds rows capacity)
      (add_le (add_le (predictAllBound_costs bounds metaCount.word.toNat width) (bounds _)) tail)
  exact add_le (refreshFreeBound_costs bounds rows capacity positions units)
    (add_le (planFreeBound_costs bounds rows capacity positions width)
      (add_le drawM (add_le (bounds _)
        (add_le (closeOptionBound_costs bounds rows capacity positions width)
          (dispatchBound_costs bounds rows capacity positions width)))))

private theorem selectBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity positions units width : Nat) :
    selectBound words rows capacity positions units width ≤
      selectBound κ rows capacity positions units width := by
  have prep : prepareBound words rows capacity positions width ≤
      prepareBound κ rows capacity positions width := by
    have inner : metaRateBound words rows capacity +
        (predictBound words positions width + words .read) ≤
        metaRateBound κ rows capacity + (predictBound κ positions width + κ .read) :=
      add_le (metaRateBound_costs bounds rows capacity)
        (add_le (predictBound_costs bounds positions width) (bounds .read))
    unfold prepareBound
    simp only [Library.work, Library.control]
    gcongr <;> exact bounds _
  have srv : serveBound words rows width ≤ serveBound κ rows width := by
    have tail : Library.ofFn.work (words .visit) rows (words .read) + words .serve ≤
        Library.ofFn.work (κ .visit) rows (κ .read) + κ .serve := by
      simp only [Library.work, Library.control]
      gcongr <;> exact bounds _
    exact add_le (predictAllBound_costs bounds rows width)
      (add_le (predictAllBound_costs bounds metaCount.word.toNat width) tail)
  have optB : optionBranchBound words rows capacity positions units width ≤
      optionBranchBound κ rows capacity positions units width :=
    add_le (potentialBound_costs bounds width) (add_le (metaRateBound_costs bounds rows capacity)
      (add_le (add_le (predictAllBound_costs bounds metaCount.word.toNat width) (bounds _))
        (add_le (comparisonBound_costs bounds metaCount.word.toNat)
          (add_le (metaRateBound_costs bounds rows capacity)
            (add_le (decideBound_costs bounds rows capacity width)
              (add_le (stepOptionBound_costs bounds rows capacity positions width)
                (add_le (closeOptionBound_costs bounds rows capacity positions width)
                  (atBoundaryBound_costs bounds rows capacity positions units width))))))))
  exact add_le prep (add_le srv (add_le (bounds _)
    (add_le (primitiveBound_costs bounds rows capacity width)
      (add_le (atBoundaryBound_costs bounds rows capacity positions units width) optB))))

theorem chooseBound_mono {words κ : Costs} (bounds : SiteBounds words κ) (interface : Interface)
    (config : Features.Config) (dimension : Dimension) :
    chooseBound words interface config dimension ≤ chooseBound κ interface config dimension :=
  add_le (bounds _) (add_le (frameBound_costs bounds interface dimension.capacity config)
    (selectBound_costs bounds interface.actions.word.toNat dimension.capacity
      (rankDimension dimension).capacity config.units.count (frameWidth interface config)))

theorem choose_learnThenAct (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    state.choose .learnThenAct percept = state.chooseSelected .learnThenAct (by decide) percept :=
  rfl

theorem choose_work (κ : Costs)
    (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (chooseSelected κ state .learnThenAct (by decide) percept).val =
        state.choose .learnThenAct percept ∧
      (chooseSelected κ state .learnThenAct (by decide) percept).work ≤
        chooseBound κ interface config dimension :=
  ⟨rfl, chooseSelected_work κ state .learnThenAct (by decide) percept⟩

theorem choose_words {words κ : Costs} (bounds : SiteBounds words κ)
    (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (chooseSelected words state .learnThenAct (by decide) percept).work ≤
      chooseBound κ interface config dimension :=
  Nat.le_trans (chooseSelected_work words state .learnThenAct (by decide) percept)
    (chooseBound_mono bounds interface config dimension)

end AcornVerif.Resource.Twin
