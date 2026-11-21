/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Mathlib.Tactic.GCongr
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Ring.Nat
import AcornVerif.Resource.SelectionWork

/-!
# Work of the first part of the step

The first part of the step under an order whose first part is selection
(`Agent.chooseSelected`): the clock, the encoding of the percept's frame and selection with
the planning that order places before the action. The work of its twin is bounded by a
function of the interface, the feature configuration and the dimension alone, for every cost
of the sites (`AcornVerif.Resource.Twin.choose_work`): the frame's active features are bounded
by the configuration (`Agent.frame_length`), every learner's eligible entries by the capacity of
its dimension, every stored frame by the same capacity, and every other loop by a count the
type of its collection fixes.

**What the bound covers.** The theorems bound the accounting of the first part's twin, which
counts each loop as the passes of its runtime implementation, with one visit for each pass's
end. None of them is a bound of the executed first part's work: reading them as one rests on a
trust assumption and correspondences that no theorem checks, part of obligation 7 of
`docs/mission-contract.md`. The trust assumption is that the compiler erases a
costed definition's work, so the definition compiles to the code of its value (`Acorn.Cost`).
The learner's, the learner record's, the policy's, the controllers' costed parts (those
`Acorn.Cost` names), the encoding's and the option models' input, ranked features,
prediction and updates, apart from the exceptions `AcornVerif.Resource.Work` states, are the work of
their executed functions, whose definitions are the values of
their costed definitions, under the cost discipline of `Acorn.Cost`: every value a costed definition
passes in, the uncosted entry points that `Acorn.Cost` lists, is computed without a costed
definition and with no loop except those `Acorn.Cost` lists as left inside a segment, whose trip
counts are bounded by constants of the code (the at most 33 steps of `Portable.pow` among them),
which is checked by reading, and no check enforces it. The other parts, among them the
controllers' initial value and reset (`Controller.initial`, `Controller.resetAction`) and selection,
are twins (`AcornVerif.Resource.Work`) whose charges were compared with the compiled call multisets
of one build by a one-time inventory, an observation of that build which no gate repeats.

**Word operations.** A site's cost in word operations is not derived from the compiled code.
`AcornVerif.Resource.Twin.choose_words` bounds the accounting of the first part's twin charged at
a cost model `words` by `chooseBound κ`, under the hypothesis `SiteBounds words κ`, which states
only `words site ≤ κ site` for every site. That `words site` counts the word operations of a
segment of the executed code, as `Acorn.Cost` defines segments, is the intended reading of
`words` and is part of no checked statement.
-/

namespace AcornVerif.Resource.Twin

open Acorn Acorn.Features Acorn.Handcrafted

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} {planning : PlanningSelection}

/-- The costed run of `Agent.chooseSelected`: the clock, the frame's encoding, and selection
with the planning the order places before the action. -/
def chooseRun (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (percept : Percept interface) : Costed Unit := do
  Costed.op (κ .choose) ()
  let prepared := state.advanceClock
  Costed.discard (frame κ prepared percept.frame)
  selectRun κ (firstPlanning order planning) prepared.control
    (prepared.frame percept.frame).active percept.frame.declared percept.reward
    percept.frame.achieved

/-- Twin of `Agent.chooseSelected`. -/
def chooseSelected (κ : Costs) (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (selects : order ≠ .actThenLearn) (percept : Percept interface) :
    Costed (Chosen interface profile config criterion dimension planning) :=
  Costed.via (state.chooseSelected order selects percept) (chooseRun κ state order percept)

/-- The most active features a frame of an interface has under a feature configuration
(`Agent.frame_length`). -/
abbrev frameWidth (interface : Interface) (config : Features.Config) : Nat :=
  config.tilings.toNat * (interface.words + interface.layout.length) + config.units.count

/-- Selection's bound grows with the width of the frame. -/
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

/-- **The bound of the accounting of the first part's twin under an order whose first part is
selection**, for every cost of the sites, every agent state and every percept: a function of the
interface, the feature configuration and the dimension. -/
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

/-- `SiteBounds words κ`: `words site ≤ κ site` for every site, a relation between two cost
models. Nothing in it ties `words` to execution, and two zero cost models satisfy it. The intended
reading of `words site` is the largest number of word operations, on the word machine of
`AcornVerif.Resource.WordKernel` with one for each instruction, of a segment at a charge point of
that site, as `Acorn.Cost` defines segments; no checked statement contains that reading. -/
def SiteBounds (words κ : Costs) : Prop := ∀ site, words site ≤ κ site

/-- Helper: a monotone step for `Library.work` of any loop helper when visit and body costs grow. -/
private theorem add_le {a b c d : Nat} (h1 : a ≤ b) (h2 : c ≤ d) : a + c ≤ b + d :=
  Nat.add_le_add h1 h2

/-- Helper: `frameBound` grows with the cost of each site. -/
private theorem frameBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (interface : Interface) (capacity : Nat) (config : Features.Config) :
    frameBound words interface capacity config ≤ frameBound κ interface capacity config := by
  simp only [frameBound, wordsBound, projectionBound, encodeBound, tiledBound, uniqueBound,
    pass, Library.work, Library.control]
  gcongr <;> exact bounds _

/-- Helper: `predictBound` grows with the cost of each site. -/
private theorem predictBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (positions width : Nat) :
    predictBound words positions width ≤ predictBound κ positions width := by
  simp only [predictBound, inputBound, lookaheadBound, outcomeValuesBound, comparisonBound,
    expectedBound, bestBound, rowInputBound, expectedAtBound, rankedValuesBound, occupiedBound,
    Library.work, Library.control]
  gcongr <;> exact bounds _

/-- Helper: `predictAllBound` grows with the cost of each site. -/
private theorem predictAllBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows width : Nat) : predictAllBound words rows width ≤ predictAllBound κ rows width := by
  simp only [predictAllBound, Library.work, Library.control]
  gcongr <;> exact bounds _

/-- Helper: `metaRateBound` grows with the cost of each site. -/
private theorem metaRateBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows width : Nat) : metaRateBound words rows width ≤ metaRateBound κ rows width := by
  simp only [metaRateBound, rateBound, normalizedBound, Library.work, Library.control]
  gcongr <;> exact bounds _

/-- Helper: `modelBeginBound` grows with the cost of each site. -/
private theorem modelBeginBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (capacity positions width : Nat) :
    modelBeginBound words capacity positions width ≤
      modelBeginBound κ capacity positions width := by
  simp only [modelBeginBound, inputBound, beginBound, transitionBeginBound, rowInputBound,
    updateRowsBound, zeroBound, secondLoopBound, pass, Library.work, Library.control]
  gcongr <;> exact bounds _

/-- Helper: `modelStepBound` grows with the cost of each site. -/
private theorem modelStepBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (capacity positions width : Nat) :
    modelStepBound words capacity positions width ≤ modelStepBound κ capacity positions width := by
  simp only [modelStepBound, inputBound, transitionStepBound, rowInputBound, updateRowsBound,
    stepBound, firstLoopBound, secondLoopBound, pass, firstVisit, Library.work, Library.control]
  gcongr <;> exact bounds _

/-- Helper: `modelTerminalWorkBound` grows with the cost of each site. -/
private theorem modelTerminalWorkBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (capacity positions width : Nat) :
    modelTerminalWorkBound words capacity positions width ≤
      modelTerminalWorkBound κ capacity positions width := by
  simp only [modelTerminalWorkBound, outcomeBound, modelTerminalBound, updateRowsBound,
    terminalBound, firstLoopBound, zeroBound, firstVisit, indicatorBound, rankedValuesBound,
    comparisonBound, expectedBound, bestBound, occupiedBound, predictAllBound, Library.work,
    Library.control]
  gcongr <;> exact bounds _

/-- Helper: `modelStopBound` grows with the cost of each site. -/
private theorem modelStopBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (capacity positions width : Nat) :
    modelStopBound words capacity positions width ≤ modelStopBound κ capacity positions width := by
  simp only [modelStopBound, outcomeBound, stopTrajectoryBound, updateRowsBound, firstLoopBound,
    releaseBound, firstVisit, indicatorBound, rankedValuesBound, comparisonBound, expectedBound,
    bestBound, occupiedBound, predictAllBound, Library.work, Library.control]
  gcongr <;> exact bounds _

/-- Helper: `optionStepBound` grows with the cost of each site. -/
private theorem optionStepBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity width : Nat) :
    optionStepBound words rows capacity width ≤ optionStepBound κ rows capacity width := by
  simp only [optionStepBound, persistentBound, policyStepBound, creditStepBound, creditBound,
    secondLoopBound, pass, firstLoopBound, zeroBound, firstVisit, greedyBound, probabilitiesBound,
    candidatesBound, bestBound, Library.work, Library.control]
  gcongr <;> exact bounds _

/-- Helper: `stepOptionBound` grows with the cost of each site. -/
private theorem stepOptionBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity positions width : Nat) :
    stepOptionBound words rows capacity positions width ≤
      stepOptionBound κ rows capacity positions width :=
  add_le (bounds _) (add_le (optionStepBound_costs bounds rows capacity width)
    (modelStepBound_costs bounds capacity positions width))

/-- Helper: `closeOptionBound` grows with the cost of each site. -/
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

/-- Helper: `decideBound` grows with the cost of each site. -/
private theorem decideBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (rows capacity width : Nat) :
    decideBound words rows capacity width ≤ decideBound κ rows capacity width := by
  simp only [decideBound, frozenBound, rateBound, normalizedBound, comparisonBound, expectedBound,
    bestBound, predictAllBound, Library.work, Library.control]
  gcongr <;> exact bounds _

/-- Helper: `settleBound` grows with the cost of each site. -/
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

/-- Helper: `planFreeBound` grows with the cost of each site. -/
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

/-- Helper: `refreshFreeBound` grows with the cost of each site. -/
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

/-- Helper: `primitiveBound` grows with the cost of each site. -/
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

/-- Helper: `potentialBound` grows with the cost of each site. -/
private theorem potentialBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (width : Nat) : potentialBound words width ≤ potentialBound κ width := by
  simp only [potentialBound, Library.control]
  gcongr <;> exact bounds _

/-- Helper: `comparisonBound` grows with the cost of each site. -/
private theorem comparisonBound_costs {words κ : Costs} (bounds : SiteBounds words κ)
    (count : Nat) : comparisonBound words count ≤ comparisonBound κ count := by
  simp only [comparisonBound, expectedBound, bestBound, Library.work, Library.control]
  gcongr <;> exact bounds _

/-- Helper: `dispatchBound` grows with the cost of each site. -/
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

/-- Helper: `atBoundaryBound` grows with the cost of each site. -/
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

/-- Helper: `selectBound` grows with the cost of each site. -/
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

/-- The first part's bound grows with the cost of each site. -/
theorem chooseBound_mono {words κ : Costs} (bounds : SiteBounds words κ) (interface : Interface)
    (config : Features.Config) (dimension : Dimension) :
    chooseBound words interface config dimension ≤ chooseBound κ interface config dimension :=
  add_le (bounds _) (add_le (frameBound_costs bounds interface dimension.capacity config)
    (selectBound_costs bounds interface.actions.word.toNat dimension.capacity
      (rankDimension dimension).capacity config.units.count (frameWidth interface config)))

/-- The first part under the default order is `Agent.chooseSelected` at `learnThenAct`. -/
theorem choose_learnThenAct (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    state.choose .learnThenAct percept = state.chooseSelected .learnThenAct (by decide) percept :=
  rfl

/-- **The work bound of the first part's twin under `learnThenAct`.** The twin's value is the
executed first part, and its accounting is at most `chooseBound`, for every cost model, agent state
and percept. It is not a bound of the executed first part's work: that reading rests on the
compiler's erasure of the work of the costed definitions of the learner, of a learner's record (its
entry, retirement and credit), of the controllers (their predictions, clear, release, snapshot,
derived rate and the updates `Acorn.Cost` names), of the frozen policy and of its
exploration, of the encoding of a frame and of an option model's input, ranked features, prediction
and updates, a trust assumption, on the cost discipline of the same costed definitions, checked by
reading, and on the twins' correspondence with the executed selection, the controllers' initial
value and reset among them, observed in one build by a one-time inventory of its compiled calls;
this linkage is part of obligation 7 of `docs/mission-contract.md`. -/
theorem choose_work (κ : Costs)
    (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (chooseSelected κ state .learnThenAct (by decide) percept).val =
        state.choose .learnThenAct percept ∧
      (chooseSelected κ state .learnThenAct (by decide) percept).work ≤
        chooseBound κ interface config dimension :=
  ⟨rfl, chooseSelected_work κ state .learnThenAct (by decide) percept⟩

/-- **The twin accounting of the first part under `learnThenAct` at a second cost model.** Under
`SiteBounds words κ`, the accounting of the first part's twin charged at `words` is at most
`chooseBound κ`, for every agent state and percept. It is not a bound of executed word operations:
that reading needs `words` to count the segments of the executed code, the intended reading of
`SiteBounds` that no checked statement contains, and in addition the compiler's erasure of the work
of the costed definitions of the learner, of a learner's record (its entry, retirement and credit),
of the controllers (their predictions, clear, release, snapshot, derived rate and the updates
`Acorn.Cost` names), of the frozen policy and of its exploration and of the encoding
of a frame and of an option model's input, ranked features, prediction and updates, a trust
assumption, the cost discipline of the same costed definitions, checked by reading, and the twins'
correspondence with the executed selection, the controllers' initial value and reset among them,
observed in one build by a one-time inventory of its compiled calls; this linkage is part of
obligation 7 of `docs/mission-contract.md`. -/
theorem choose_words {words κ : Costs} (bounds : SiteBounds words κ)
    (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (chooseSelected words state .learnThenAct (by decide) percept).work ≤
      chooseBound κ interface config dimension :=
  Nat.le_trans (chooseSelected_work words state .learnThenAct (by decide) percept)
    (chooseBound_mono bounds interface config dimension)

end AcornVerif.Resource.Twin
