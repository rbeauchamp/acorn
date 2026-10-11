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

**What the bound covers.** The theorems bound the work of the first part's twin, which
counts each loop as the passes of its runtime implementation, with one visit for each pass's
end. Read as the work of the executed first part, they rest on a trust assumption and two
correspondences that no theorem checks. The trust assumption is that the compiler erases a
costed definition's work, so the definition compiles to the code of its value (`Acorn.Cost`).
The learner's part is the work of the executed learner, whose definitions are the values of
their costed definitions, under the cost discipline of `Acorn.Cost`: every value
a costed definition passes in, the uncosted entry points that `Acorn.Cost` lists, is computed
without a loop and without a costed definition, which is checked by reading until
rbeauchamp/regula#333 checks it.
The other parts, the encoding and selection among them, are twins (`AcornVerif.Resource.Work`)
whose charges were compared with the compiled call multisets of one build by a one-time
inventory, an observation of that build which no gate repeats.

**Word operations.** A site's cost in word operations is not derived from the compiled code. The
bound in word operations (`AcornVerif.Resource.Twin.choose_words`) holds under the hypothesis
`SiteBounds words κ`: the segment of each charge of a site runs at most `κ site` word
operations.
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
theorem selectBound_mono (κ : Costs) (rows capacity positions questions units : Nat)
    {width limit : Nat} (fits : width ≤ limit) :
    selectBound κ rows capacity positions questions units width ≤
      selectBound κ rows capacity positions questions units limit := by
  simp only [selectBound, prepareBound, serveBound, primitiveBound, atBoundaryBound,
    optionBranchBound, planFreeBound, drawMetaBound, closeOptionBound, dispatchBound,
    planningBound, backupAllBound, lookAheadBound, predictBound, inputBound, lookaheadBound,
    outcomeValuesBound, rowInputBound, expectedAtBound, planBound, predictAllBound,
    potentialBound, decideBound, frozenBound, stepOptionBound, stepTemporalBound, optionStepBound,
    policyStepBound, creditStepBound, secondLoopBound, modelStepBound, transitionStepBound,
    stepBound, updateRowsBound, endTemporalBound, modelTerminalWorkBound, outcomeBound,
    indicatorBound, settleBound, stopFollowingBound, modelStopBound, beginTemporalBound,
    beginOptionBound, modelBeginBound, transitionBeginBound, beginBound, learnMetaBound, pass,
    Library.work, Library.control, Library.passes]
  gcongr

/-- **The work of the first part of the step under an order whose first part is selection**,
for every cost of the sites, every agent state and every percept: a function of the
interface, the feature configuration and the dimension. -/
abbrev chooseBound (κ : Costs) (interface : Interface) (config : Features.Config)
    (dimension : Dimension) : Nat :=
  κ .choose + (frameBound κ interface dimension.capacity config +
    selectBound κ interface.actions.word.toNat dimension.capacity
      (rankDimension dimension).capacity (interface.signals.length + 1) config.units.count
      (frameWidth interface config))

theorem chooseSelected_work (κ : Costs)
    (state : Agent interface profile config criterion dimension planning)
    (order : StepOrder) (selects : order ≠ .actThenLearn) (percept : Percept interface) :
    (chooseSelected κ state order selects percept).work ≤
      chooseBound κ interface config dimension :=
  Costed.bind_work_le (Nat.le_refl _) fun _ =>
    Costed.bind_work_le (frame_work κ _ percept.frame) fun _ =>
      Nat.le_trans (selectRun_work κ _ _ _ _ _ _)
        (selectBound_mono κ _ _ _ _ _ (Agent.frame_length _ percept.frame))

/-- `SiteBounds words κ`: the segment of each charge of a site runs at most `κ site` word
operations, where `words site` is the largest number of word operations of the segment of a charge
of that site on the word machine of `AcornVerif.Resource.WordKernel`, one for each instruction.
Every operation of a decision belongs to the segment of the first charge at or after it in execution
order, and the operations after the last charge to that last charge, so each operation is in exactly
one segment (`Acorn.Cost`). A site's docstring names the operations its charge marks; where a site
is charged before a nested computation that makes its own charges, the named operations that run
after that nested charge are counted in a later charge's segment. Every segment is bounded by a
constant of the code, so `words` is a finite hypothesis. No theorem derives `words`; a bound in word
operations holds under this hypothesis. -/
def SiteBounds (words κ : Costs) : Prop := ∀ site, words site ≤ κ site

set_option maxHeartbeats 400000 in
-- The unfolded bound has one monotone step for each loop of the first part.
/-- The first part's bound grows with the cost of each site. -/
theorem chooseBound_mono {words κ : Costs} (bounds : SiteBounds words κ) (interface : Interface)
    (config : Features.Config) (dimension : Dimension) :
    chooseBound words interface config dimension ≤ chooseBound κ interface config dimension := by
  simp only [chooseBound, atBoundaryBound, backupAllBound, bankInitialBound, beginBound,
    beginOptionBound, beginTemporalBound, bestBound, candidateListBound, candidatesBound,
    changedBound, clearBound, closeOptionBound, columnsBound, comparisonBound,
    controllerInitialBound, creditBound, creditStepBound, decideBound, dispatchBound,
    drawMetaBound, encodeBound, endTemporalBound, expectedAtBound, expectedBound,
    firstLoopBound, firstVisit, forgetBound, frameBound, frozenBound, greedyBound,
    indicatorBound, inputBound, installBound, learnMetaBound, learnerInitialBound,
    lookAheadBound, lookaheadBound, mergedBound, metaRateBound, modelBeginBound,
    modelInitialBound, modelStepBound, modelStopBound, modelTerminalBound,
    modelTerminalWorkBound, normalizedBound, occupiedBound, optionBranchBound, optionStepBound,
    outcomeBound, outcomeValuesBound, persistentBound, planBound, planFreeBound, planningBound,
    policyStepBound, potentialBound, predictAllBound, predictBound, prepareBound,
    primitiveBound, probabilitiesBound, projectionBound, questionsInitialBound, rankedBound,
    rankedCandidatesBound, rankedEmptyBound, rankedRerankBound, rankedSlotsBound,
    rankedValuesBound, rateBound, refreshBound, refreshFreeBound, refreshRankedBound,
    releaseBound, rerankModelsBound, rowInputBound, secondLoopBound, selectBound, serveBound,
    settleBound, skillInitialBound, stepBound, stepOptionBound, stepTemporalBound, stopBound,
    stopFollowingBound, stopTrajectoryBound, sweepAllBound, tabulateBound, terminalBound,
    terminalCreditBound, tiledBound, transitionBeginBound, transitionInitialBound,
    transitionRerankBound, transitionStepBound, uniqueBound, updateRowsBound, wordsBound,
    zeroBound, pass, Library.work, Library.control]
  gcongr <;> exact bounds _

/-- The first part under the default order is `Agent.chooseSelected` at `learnThenAct`. -/
theorem choose_learnThenAct (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    state.choose .learnThenAct percept = state.chooseSelected .learnThenAct (by decide) percept :=
  rfl

/-- **The work bound of the first part's twin under `learnThenAct`.** The twin's value is the
executed first part, and its work is at most `chooseBound`, for every cost model, agent state
and percept. As the work of the executed first part it rests on the compiler's erasure of the
costed learner's work, a trust assumption, on the cost discipline of the costed learner, checked
by reading, and on the twins' correspondence with the executed encoding and selection, observed
in one build by a one-time inventory of its compiled calls. -/
theorem choose_work (κ : Costs)
    (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (chooseSelected κ state .learnThenAct (by decide) percept).val =
        state.choose .learnThenAct percept ∧
      (chooseSelected κ state .learnThenAct (by decide) percept).work ≤
        chooseBound κ interface config dimension :=
  ⟨rfl, chooseSelected_work κ state .learnThenAct (by decide) percept⟩

/-- **The twin accounting of the first part under `learnThenAct` in word operations.** If the
segment of each charge of a site runs at most `κ site` word operations, the work of the first part's
twin counted in the word operations of its sites is at most `chooseBound κ`, for every agent state
and percept. Read as the word operations of the executed first part, it rests in addition on the
compiler's erasure of the costed learner's work, a trust assumption, on the cost discipline of the
costed learner, checked by reading, and on the twins' correspondence with the executed encoding and
selection, observed in one build by a one-time inventory of its compiled calls. -/
theorem choose_words {words κ : Costs} (bounds : SiteBounds words κ)
    (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (chooseSelected words state .learnThenAct (by decide) percept).work ≤
      chooseBound κ interface config dimension :=
  Nat.le_trans (chooseSelected_work words state .learnThenAct (by decide) percept)
    (chooseBound_mono bounds interface config dimension)

end AcornVerif.Resource.Twin
