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
the planning that order places before the action. Its work is bounded by a function of the
interface, the feature configuration and the dimension alone, for every cost of the sites
(`AcornVerif.Resource.Twin.choose_work`): the frame's active features are bounded by the
configuration (`Agent.frame_length`), every learner's eligible entries by the capacity of
its dimension, every stored frame by the same capacity, and every other loop by a count the
type of its collection fixes.
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
    beginOptionBound, modelBeginBound, transitionBeginBound, beginBound, learnMetaBound]
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

/-- The first part under the default order is `Agent.chooseSelected` at `learnThenAct`. -/
theorem choose_learnThenAct (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    state.choose .learnThenAct percept = state.chooseSelected .learnThenAct (by decide) percept :=
  rfl

/-- **The work bound of the first part under `learnThenAct`.** The twin's value is the
executed first part, and its work is at most `chooseBound`, for every cost model, agent state
and percept. -/
theorem choose_work (κ : Costs)
    (state : Agent interface profile config criterion dimension planning)
    (percept : Percept interface) :
    (chooseSelected κ state .learnThenAct (by decide) percept).val =
        state.choose .learnThenAct percept ∧
      (chooseSelected κ state .learnThenAct (by decide) percept).work ≤
        chooseBound κ interface config dimension :=
  ⟨rfl, chooseSelected_work κ state .learnThenAct (by decide) percept⟩

end AcornVerif.Resource.Twin
