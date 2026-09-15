/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Sarsa

/-!
# Current action selection and frozen policy observations

The ordered near-maximum reservoir is Acorn's PAR-2 adaptation of Javed &
Sutton, *Swift-Sarsa: Fast and Robust Linear Control*, arXiv:2507.19539v1
(2025), Algorithm 1. It is not the paper's arg-max. Multiply-high bins and
53-bit branch draws retain the current RNG's finite-word law. Reported masses
are nominal binary32 epsilon masses, not exact probabilities of those bins.
-/
namespace Acorn.Features

/-- The generated binary32 tie-window word. -/
def tieWindow : Binary32 := ⟨AcornSpec.Constants.tie1e6Bits⟩

/-- Frozen raw values and bounded epsilon over a nonempty machine action space. -/
structure PolicySnapshot (count : Word.Count) where
  /-- Values captured before the draw and subsequent learner writes. -/
  values : Vector Binary32 count.word.toNat
  /-- Stored epsilon in its closed interval. -/
  epsilon : SwiftTd.ExploreRate

variable {count : Word.Count}

/-- First action is available by the receiving count's own positive bound. -/
def firstAction (count : Word.Count) : Action count.word.toNat := ⟨0, count.positive⟩

/-- Ordered maximum uses IEEE comparisons, including the raw NaN fallback. -/
def PolicySnapshot.best (snapshot : PolicySnapshot count) : Binary32 :=
  snapshot.values.toList.drop 1 |>.foldl
    (fun best value => if best.less value then value else best)
    (snapshot.values.get (firstAction count))

/-- Candidates retain original action order and the exact subtraction/comparison. -/
def PolicySnapshot.candidates (snapshot : PolicySnapshot count) : List (Action count.word.toNat) :=
  let threshold := snapshot.best.sub tieWindow
  (List.finRange count.word.toNat).filter fun action =>
    threshold.lessOrEqual (snapshot.values.get action)

/-- Ordered size-one reservoir, with one RNG draw for every candidate including
its first member. Empty candidates retain the initial fallback action. -/
def reservoir {actions : Nat} (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256) : Action actions × Rng.Xoshiro256 :=
  match pending with
  | [] => (pick, rng)
  | action :: rest =>
    let seen := seen + 1
    let draw := rng.nextBelow (Word.Count.ofWord seen)
    reservoir rest seen (if draw.1.val == 0 then action else pick) draw.2

/-- A reservoir can return only its fallback or an actual supplied candidate. -/
theorem reservoir_support {actions : Nat} (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256) :
    (reservoir pending seen pick rng).1 = pick ∨ (reservoir pending seen pick rng).1 ∈ pending := by
  induction pending generalizing seen pick rng with
  | nil => exact Or.inl rfl
  | cons action rest ih =>
    simp only [reservoir]
    split
    · rcases ih (seen + 1) action (rng.nextBelow (Word.Count.ofWord (seen + 1))).2 with h | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · rcases ih (seen + 1) pick (rng.nextBelow (Word.Count.ofWord (seen + 1))).2 with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))

/-- The first reservoir draw selects its sole candidate for every RNG state. -/
theorem first_reservoir_draw (rng : Rng.Xoshiro256) :
    (rng.nextBelow (Word.Count.ofWord 1)).1.val = 0 := by
  have bound := (rng.nextBelow (Word.Count.ofWord 1)).1.property
  have zero : (rng.nextBelow (Word.Count.ofWord 1)).1.val.toNat = 0 := by
    change (rng.nextBelow (Word.Count.ofWord 1)).1.val.toNat < 1 at bound
    omega
  exact UInt64.toNat_inj.mp zero

/-- A nonempty fresh reservoir returns a supplied candidate, with no fallback. -/
theorem reservoir_nonempty {actions : Nat} (action : Action actions)
    (rest : List (Action actions)) (pick : Action actions) (rng : Rng.Xoshiro256) :
    (reservoir (action :: rest) 0 pick rng).1 ∈ action :: rest := by
  change (reservoir rest 1
    (if (rng.nextBelow (Word.Count.ofWord 1)).1.val == 0 then action else pick)
    (rng.nextBelow (Word.Count.ofWord 1)).2).1 ∈ action :: rest
  rw [first_reservoir_draw]
  simp only [beq_self_eq_true, if_true]
  rcases reservoir_support rest 1 action (rng.nextBelow (Word.Count.ofWord 1)).2 with h | h
  · exact List.mem_cons.mpr (Or.inl h)
  · exact List.mem_cons.mpr (Or.inr h)

/-- Greedy draw preserves the current raw-domain fallback and reservoir order. -/
def PolicySnapshot.greedy (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Action count.word.toNat × Rng.Xoshiro256 :=
  reservoir snapshot.candidates 0 (firstAction count) rng

/-- Uniform branch consumes one multiply-high draw with its own range proof. -/
def uniformAction (count : Word.Count) (rng : Rng.Xoshiro256) :
    Action count.word.toNat × Rng.Xoshiro256 :=
  let result := rng.nextBelow count
  (⟨result.1.val.toNat, result.1.property⟩, result.2)

/-- Nominal telemetry masses are calculated without consuming random state. -/
def PolicySnapshot.probabilities (snapshot : PolicySnapshot count) : Vector Binary32 count.word.toNat :=
  let explore := snapshot.epsilon.value.div (Binary32.ofUInt64 count.word)
  let greedy := (Binary32.one.sub snapshot.epsilon.value).div
    (Binary32.ofUInt64 snapshot.candidates.length.toUInt64)
  let threshold := snapshot.best.sub tieWindow
  snapshot.values.map fun value => explore.add
    (if threshold.lessOrEqual value then greedy else .zero)

/-- A completed draw carries exactly the snapshot from which its action came. -/
structure PolicyDecision (count : Word.Count) where
  private mk ::
  /-- Immutable values and epsilon used for this draw. -/
  snapshot : PolicySnapshot count
  /-- Same admitted action used for selection, update and observation. -/
  action : Action count.word.toNat
  /-- Whether the branch draw chose exploration. -/
  explored : Bool

/-- One epsilon draw followed by precisely the selected branch's RNG operations. -/
def PolicySnapshot.draw (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    PolicyDecision count × Rng.Xoshiro256 :=
  let branch := rng.nextF64
  let explored := branch.1.less (Conversion.widen snapshot.epsilon.value)
  let chosen := if explored then uniformAction count branch.2 else snapshot.greedy branch.2
  (⟨snapshot, chosen.1, explored⟩, chosen.2)

/-- Differential continuation observes the value of the actual sampled action. -/
def PolicyDecision.continuation (decision : PolicyDecision count) : Binary32 :=
  decision.snapshot.values.get decision.action

/-- Decision telemetry is a pure observation of the frozen snapshot. -/
def PolicyDecision.probabilities (decision : PolicyDecision count) : Vector Binary32 count.word.toNat :=
  decision.snapshot.probabilities

/-- Sampled continuation and reported selected value are definitionally identical. -/
theorem PolicyDecision.continuation_selected (decision : PolicyDecision count) :
    decision.continuation = decision.snapshot.values.get decision.action := rfl

/-- Every draw retains the exact pre-draw snapshot. -/
theorem PolicySnapshot.draw_snapshot (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (snapshot.draw rng).1.snapshot = snapshot := rfl

/-- The runtime action is always admitted, independent of all value words. -/
theorem PolicySnapshot.draw_admitted (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (snapshot.draw rng).1.action.val < count.word.toNat := (snapshot.draw rng).1.action.isLt

/-- Frozen-decision SMDP credit uses the sampled action and its original values. -/
def Controller.policyStep {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (decision : PolicyDecision count)
    (reward : Binary32) (duration : UInt32) : Controller config dimension count.word.toNat :=
  controller.valuesStep features decision.snapshot.values decision.action reward
    (Portable.pow config.rule.gamma duration) (Portable.pow controller.traceDecay duration)

/-- Freeze current controller values with the caller's resolved rate. -/
def Controller.snapshot {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (epsilon : SwiftTd.ExploreRate) : PolicySnapshot count :=
  ⟨controller.predictAll features, epsilon⟩

/-- PAR-10 concatenates eligible pairs across all action learners in order.
This is Acorn's own normalized-step-size map, not a Swift-Sarsa equation. -/
def Controller.exploreRate {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat) : SwiftTd.ExploreRate :=
  let totals := controller.learners.toList.foldl (fun (sum, count) learner =>
    let contribution := learner.state.normalizedStepSizeSum
    (sum.add contribution.1, count + contribution.2)) (Binary32.zero, 0)
  SwiftTd.ExploreRate.project <| if totals.2 == 0 then
    (controller.learners.get (firstAction count)).state.initialNormalizedStepSize config
  else totals.1.div (Binary32.ofUInt64 totals.2.toUInt64)

/-- Nominal epsilon mean uses widened ordered sums and the input convex hull.
The projection contains rounding only; raw malformed vectors keep total float
semantics. Terminal learning uses the sampled continuation instead of this mean. -/
def PolicySnapshot.expected (snapshot : PolicySnapshot count) : Binary32 :=
  let first := snapshot.values.get (firstAction count)
  let lower := snapshot.values.toList.foldl (fun lo v => if v.less lo then v else lo) first
  let upper := snapshot.best
  let threshold := upper.sub tieWindow
  let totals := snapshot.values.toList.foldl (fun (all, tied, n) v =>
    (all.add (Conversion.widen v),
      if threshold.lessOrEqual v then tied.add (Conversion.widen v) else tied,
      if threshold.lessOrEqual v then n + 1 else n)) (Binary64.ofUInt64 0, Binary64.ofUInt64 0, 0)
  let eps := Conversion.widen snapshot.epsilon.value
  let value := ((Binary64.ofUInt64 1).sub eps).mul
    (totals.2.1.div (Binary64.ofUInt64 totals.2.2.toUInt64))
  let value := value.add (eps.mul (totals.1.div (Binary64.ofUInt64 count.word)))
  (Conversion.narrow value).saturate lower upper

end Acorn.Features
