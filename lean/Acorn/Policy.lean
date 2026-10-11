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

Credit for an action the frozen policy did not draw follows Precup, Sutton &
Singh, *Eligibility Traces for Off-Policy Policy Evaluation*, ICML (2000), §4,
Algorithm 2 (tree backup): it reads the frozen policy's own nominal masses and
no probability of the policy that selected the action.
-/
namespace Acorn.Features

/-- The generated binary32 tie-window word. -/
def tieWindow : Binary32 := ⟨Acorn.Constants.tie1e6Bits⟩

/-- Frozen raw values and bounded epsilon over a nonempty machine action space. -/
structure PolicySnapshot (count : Word.Count) where
  /-- Values captured before the draw and subsequent learner writes. -/
  values : Vector Binary32 count.word.toNat
  /-- Stored epsilon in its closed interval. -/
  epsilon : SwiftTd.ExploreRate

variable {count : Word.Count}

/-- First action is available by the receiving count's own positive bound. -/
def firstAction (count : Word.Count) : Action count.word.toNat := ⟨0, count.positive⟩

/-- The ordered maximum with its work: the first value read, the values listed, the first one
dropped, then one comparison for each other value. -/
def PolicySnapshot.bestCosted (snapshot : PolicySnapshot count) : Costed Binary32 := do
  let first ← Costed.op .read (snapshot.values.get (firstAction count))
  let skip := 1
  let values ← Costed.toList snapshot.values
  let rest ← Costed.drop skip values
  Costed.foldl (fun best value => Costed.op .compare (if best.Less value then value else best))
    first rest

/-- Ordered maximum uses IEEE comparisons, including the raw NaN fallback. -/
def PolicySnapshot.best (snapshot : PolicySnapshot count) : Binary32 :=
  snapshot.bestCosted.val

/-- The ordered maximum is the fold of the comparison over the values after the first. -/
theorem PolicySnapshot.best_def (snapshot : PolicySnapshot count) :
    snapshot.best = (snapshot.values.toList.drop 1).foldl
      (fun best value => if best.Less value then value else best)
      (snapshot.values.get (firstAction count)) := rfl

/-- The near-maximum candidates with their work: the maximum, the tie threshold, the action
list, then one test for each action. -/
def PolicySnapshot.candidatesCosted (snapshot : PolicySnapshot count) :
    Costed (List (Action count.word.toNat)) := do
  let top ← snapshot.bestCosted
  let threshold ← Costed.op .tieThreshold (top.sub tieWindow)
  let range ← Costed.finRange count.word.toNat
  Costed.filter (fun action => Costed.op .candidate
    (decide (threshold.LessOrEqual (snapshot.values.get action)))) range

/-- Candidates retain original action order and the exact subtraction/comparison. -/
def PolicySnapshot.candidates (snapshot : PolicySnapshot count) : List (Action count.word.toNat) :=
  snapshot.candidatesCosted.val

/-- The candidates are the actions whose value is within the tie window of the maximum. -/
theorem PolicySnapshot.candidates_def (snapshot : PolicySnapshot count) :
    snapshot.candidates =
      let threshold := snapshot.best.sub tieWindow
      (List.finRange count.word.toNat).filter fun action =>
        decide (threshold.LessOrEqual (snapshot.values.get action)) := rfl

/-- The ordered size-one reservoir with its work, by the same recursion: one draw for each
pending candidate, charged before the next level, and a visit for its end. -/
def reservoirCosted {actions : Nat} : List (Action actions) → UInt64 → Action actions →
    Rng.Xoshiro256 → Costed (Action actions × Rng.Xoshiro256)
  | [], _, pick, rng => Costed.op .visit (pick, rng)
  | action :: rest, seen, pick, rng =>
    let seen := seen + 1
    let draw := rng.nextBelow (Word.Count.ofWord seen)
    Costed.charge .visit <| Costed.charge .reservoirDraw <|
      reservoirCosted rest seen (if draw.1.val == 0 then action else pick) draw.2

/-- Ordered size-one reservoir, with one RNG draw for every candidate including
its first member. Empty candidates retain the initial fallback action. -/
def reservoir {actions : Nat} (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256) : Action actions × Rng.Xoshiro256 :=
  (reservoirCosted pending seen pick rng).val

/-- An empty reservoir returns its fallback and the generator unchanged. -/
theorem reservoir_nil {actions : Nat} (seen : UInt64) (pick : Action actions)
    (rng : Rng.Xoshiro256) : reservoir [] seen pick rng = (pick, rng) := rfl

/-- Each candidate takes one draw, and the draw's zero picks it. -/
theorem reservoir_cons {actions : Nat} (action : Action actions) (rest : List (Action actions))
    (seen : UInt64) (pick : Action actions) (rng : Rng.Xoshiro256) :
    reservoir (action :: rest) seen pick rng =
      let seen := seen + 1
      let draw := rng.nextBelow (Word.Count.ofWord seen)
      reservoir rest seen (if draw.1.val == 0 then action else pick) draw.2 := rfl

/-- The reservoir is the recursion over the pending candidates. -/
theorem reservoir_def {actions : Nat} (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256) :
    reservoir pending seen pick rng =
      match pending with
      | [] => (pick, rng)
      | action :: rest =>
        let seen := seen + 1
        let draw := rng.nextBelow (Word.Count.ofWord seen)
        reservoir rest seen (if draw.1.val == 0 then action else pick) draw.2 := by
  cases pending <;> rfl

/-- A reservoir can return only its fallback or an actual supplied candidate. -/
theorem reservoir_support {actions : Nat} (pending : List (Action actions)) (seen : UInt64)
    (pick : Action actions) (rng : Rng.Xoshiro256) :
    (reservoir pending seen pick rng).1 = pick ∨ (reservoir pending seen pick rng).1 ∈ pending := by
  induction pending generalizing seen pick rng with
  | nil => exact Or.inl rfl
  | cons action rest ih =>
    simp only [reservoir_cons]
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
  rw [reservoir_cons]
  change (reservoir rest 1
    (if (rng.nextBelow (Word.Count.ofWord 1)).1.val == 0 then action else pick)
    (rng.nextBelow (Word.Count.ofWord 1)).2).1 ∈ action :: rest
  rw [first_reservoir_draw]
  simp only [beq_self_eq_true, ite_true]
  rcases reservoir_support rest 1 action (rng.nextBelow (Word.Count.ofWord 1)).2 with h | h
  · exact List.mem_cons.mpr (Or.inl h)
  · exact List.mem_cons.mpr (Or.inr h)

/-- The greedy draw with its work: the candidates, then the reservoir over them. -/
def PolicySnapshot.greedyCosted (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Costed (Action count.word.toNat × Rng.Xoshiro256) := do
  let pending ← snapshot.candidatesCosted
  reservoirCosted pending 0 (firstAction count) rng

/-- Greedy draw preserves the current raw-domain fallback and reservoir order. -/
def PolicySnapshot.greedy (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Action count.word.toNat × Rng.Xoshiro256 :=
  (snapshot.greedyCosted rng).val

/-- The greedy draw is the reservoir over the candidates. -/
theorem PolicySnapshot.greedy_def (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    snapshot.greedy rng = reservoir snapshot.candidates 0 (firstAction count) rng := rfl

/-- Uniform branch consumes one multiply-high draw with its own range proof. -/
def uniformAction (count : Word.Count) (rng : Rng.Xoshiro256) :
    Action count.word.toNat × Rng.Xoshiro256 :=
  let result := rng.nextBelow count
  (⟨result.1.val.toNat, result.1.property⟩, result.2)

/-- The nominal masses with their work: the candidates and their count, the maximum, then one
mass for each action. -/
def PolicySnapshot.probabilitiesCosted (snapshot : PolicySnapshot count) :
    Costed (Vector Binary32 count.word.toNat) := do
  let explore := snapshot.epsilon.value.div (Binary32.ofUInt64 count.word)
  let complement := Binary32.one.sub snapshot.epsilon.value
  let pending ← snapshot.candidatesCosted
  let size ← Costed.length pending
  let greedy := complement.div (Binary32.ofUInt64 size.toUInt64)
  let top ← snapshot.bestCosted
  let threshold := top.sub tieWindow
  Costed.charge .probabilitiesOpen <| Costed.mapVector (fun value => Costed.op .probability
    (explore.add (if threshold.LessOrEqual value then greedy else .zero))) snapshot.values

/-- Nominal masses are calculated without consuming random state. Telemetry reports
them, and off-policy option credit reads them through `consistent` and `mass`. -/
def PolicySnapshot.probabilities (snapshot : PolicySnapshot count) : Vector Binary32 count.word.toNat :=
  snapshot.probabilitiesCosted.val

/-- Each mass is the exploration share, plus the greedy share for a candidate. -/
theorem PolicySnapshot.probabilities_def (snapshot : PolicySnapshot count) :
    snapshot.probabilities =
      let explore := snapshot.epsilon.value.div (Binary32.ofUInt64 count.word)
      let greedy := (Binary32.one.sub snapshot.epsilon.value).div
        (Binary32.ofUInt64 snapshot.candidates.length.toUInt64)
      let threshold := snapshot.best.sub tieWindow
      snapshot.values.map fun value => explore.add
        (if threshold.LessOrEqual value then greedy else .zero) := rfl

/-- The ordered maximum is the fold of the strict word comparison: `best` decides
`Binary32.Less` with the instance that runs `Binary32.less`. -/
theorem PolicySnapshot.best_less (snapshot : PolicySnapshot count) :
    snapshot.best = (snapshot.values.toList.drop 1).foldl
      (fun best value => if best.less value then value else best)
      (snapshot.values.get (firstAction count)) := by
  simp only [PolicySnapshot.best_def, Binary32.less_iff]

/-- A completed draw carries exactly the snapshot from which its action came; a decision read
back from a checkpoint image carries the snapshot stored with it (`PolicyDecision.stored`). -/
structure PolicyDecision (count : Word.Count) where
  private mk ::
  /-- Immutable values and epsilon used for this draw. -/
  snapshot : PolicySnapshot count
  /-- Same admitted action used for selection, update and observation. -/
  action : Action count.word.toNat
  /-- Whether the branch draw chose exploration. -/
  explored : Bool

/-- The decision that a checkpoint image holds: the stored snapshot, action and branch.
The checkpoint loader is its one caller, and it rebuilds the decision of the saved agent
(`Checkpoint.policyDecisionFormat`). -/
def PolicyDecision.stored (snapshot : PolicySnapshot count) (action : Action count.word.toNat)
    (explored : Bool) : PolicyDecision count := ⟨snapshot, action, explored⟩

/-- The draw with its work: the branch draw, then the uniform or the greedy draw. -/
def PolicySnapshot.drawCosted (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    Costed (PolicyDecision count × Rng.Xoshiro256) :=
  let branch := rng.nextF64
  let explored := branch.1.less (Conversion.widen snapshot.epsilon.value)
  Costed.charge .drawClose <| Costed.bind
    (if explored then Costed.op .uniform (uniformAction count branch.2)
      else snapshot.greedyCosted branch.2)
    fun chosen => Costed.pure (⟨snapshot, chosen.1, explored⟩, chosen.2)

/-- One epsilon draw followed by precisely the selected branch's RNG operations. -/
def PolicySnapshot.draw (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    PolicyDecision count × Rng.Xoshiro256 :=
  (snapshot.drawCosted rng).val

/-- A draw takes the branch draw, then the uniform or the greedy draw. -/
theorem PolicySnapshot.draw_def (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    snapshot.draw rng =
      let branch := rng.nextF64
      let explored := branch.1.less (Conversion.widen snapshot.epsilon.value)
      let chosen := if explored then uniformAction count branch.2 else snapshot.greedy branch.2
      (⟨snapshot, chosen.1, explored⟩, chosen.2) := by
  unfold PolicySnapshot.draw PolicySnapshot.drawCosted
  dsimp only
  cases rng.nextF64.1.less (Conversion.widen snapshot.epsilon.value) <;> rfl

/-- Differential continuation observes the value of the actual sampled action. -/
def PolicyDecision.continuation (decision : PolicyDecision count) : Binary32 :=
  decision.snapshot.values.get decision.action

/-- A decision's reported masses are a pure observation of its frozen snapshot. -/
def PolicyDecision.probabilities (decision : PolicyDecision count) : Vector Binary32 count.word.toNat :=
  decision.snapshot.probabilities

/-- Sampled continuation and reported selected value are definitionally identical. -/
theorem PolicyDecision.continuation_selected (decision : PolicyDecision count) :
    decision.continuation = decision.snapshot.values.get decision.action := rfl

/-- Every draw retains the exact pre-draw snapshot. -/
theorem PolicySnapshot.draw_snapshot (snapshot : PolicySnapshot count) (rng : Rng.Xoshiro256) :
    (snapshot.draw rng).1.snapshot = snapshot := by
  rw [PolicySnapshot.draw_def]

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

/-- The policy mean with its work: the first value read, the values listed once, then the lower
bound, the maximum, the tie threshold and the totals, each fold a pass over the list. -/
def PolicySnapshot.expectedCosted (snapshot : PolicySnapshot count) : Costed Binary32 := do
  let first ← Costed.op .read (snapshot.values.get (firstAction count))
  let values ← Costed.toList snapshot.values
  let lower ← Costed.foldl (fun lo v => Costed.op .compare (if v.less lo then v else lo))
    first values
  let upper ← snapshot.bestCosted
  let threshold ← Costed.op .tieThreshold (upper.sub tieWindow)
  let totals ← Costed.foldl (fun (all, tied, n) v => Costed.op .expectedTerm
    (all.add (Conversion.widen v),
      if threshold.lessOrEqual v then tied.add (Conversion.widen v) else tied,
      if threshold.lessOrEqual v then n + 1 else n))
    (Binary64.ofUInt64 0, Binary64.ofUInt64 0, 0) values
  let eps := Conversion.widen snapshot.epsilon.value
  let value := ((Binary64.ofUInt64 1).sub eps).mul
    (totals.2.1.div (Binary64.ofUInt64 totals.2.2.toUInt64))
  let value := value.add (eps.mul (totals.1.div (Binary64.ofUInt64 count.word)))
  Costed.op .expectedClose ((Conversion.narrow value).saturate lower upper)

/-- Nominal epsilon mean uses widened ordered sums and the input convex hull.
The projection contains rounding only; raw malformed vectors keep total float
semantics. Terminal learning uses the sampled continuation instead of this mean. -/
def PolicySnapshot.expected (snapshot : PolicySnapshot count) : Binary32 :=
  snapshot.expectedCosted.val

/-- The policy mean is the lower bound, the maximum and the widened totals, each fold a pass
over the values. -/
theorem PolicySnapshot.expected_def (snapshot : PolicySnapshot count) :
    snapshot.expected =
      let first := snapshot.values.get (firstAction count)
      let lower := snapshot.values.toList.foldl (fun lo v => if v.less lo then v else lo) first
      let upper := snapshot.best
      let threshold := upper.sub tieWindow
      let totals := snapshot.values.toList.foldl (fun (all, tied, n) v =>
        (all.add (Conversion.widen v),
          if threshold.lessOrEqual v then tied.add (Conversion.widen v) else tied,
          if threshold.lessOrEqual v then n + 1 else n))
        (Binary64.ofUInt64 0, Binary64.ofUInt64 0, 0)
      let eps := Conversion.widen snapshot.epsilon.value
      let value := ((Binary64.ofUInt64 1).sub eps).mul
        (totals.2.1.div (Binary64.ofUInt64 totals.2.2.toUInt64))
      let value := value.add (eps.mul (totals.1.div (Binary64.ofUInt64 count.word)))
      (Conversion.narrow value).saturate lower upper := rfl

/-- Whether the frame's action was selected with this policy's own distribution:
the behaviour's reported masses equal the frozen policy's nominal masses, word for
word. Sutton, Precup & Singh, *Between MDPs and semi-MDPs*, Artificial
Intelligence 112 (1999), §5, p. 202, call an action consistent with an option when
it "was selected with the distribution π(s_t, ·)". The test reads no action: every
action of a consistent frame is a sample of the policy, exploratory ones included.
A served exploratory step reports a point mass and so matches no policy that
gives two actions positive mass. -/
def PolicySnapshot.consistent (snapshot : PolicySnapshot count)
    (behaviour : Vector Binary32 count.word.toNat) : Bool :=
  decide (snapshot.probabilities = behaviour)

/-- Consistency is equality of the two mass vectors. -/
theorem PolicySnapshot.consistent_iff (snapshot : PolicySnapshot count)
    (behaviour : Vector Binary32 count.word.toNat) :
    snapshot.consistent behaviour = true ↔ snapshot.probabilities = behaviour := by
  simp [PolicySnapshot.consistent]

/-- On a consistent frame every action has the same reported mass under the
behaviour as under the frozen policy, so an importance ratio of the two is one
wherever it is defined. -/
theorem PolicySnapshot.consistent_mass (snapshot : PolicySnapshot count)
    (behaviour : Vector Binary32 count.word.toNat) (action : Action count.word.toNat)
    (consistent : snapshot.consistent behaviour = true) :
    snapshot.probabilities.get action = behaviour.get action := by
  rw [(snapshot.consistent_iff behaviour).mp consistent]

/-- A policy's own decision is consistent with it: the masses a draw reports are
those of the snapshot it was drawn from. -/
theorem PolicyDecision.consistent_own (decision : PolicyDecision count) :
    decision.snapshot.consistent decision.probabilities = true :=
  (decision.snapshot.consistent_iff _).mpr rfl

/-- Nominal mass of one action under the frozen ε-greedy policy: the word
`probabilities` reports, admitted as a probability. A NaN mass admits as zero. -/
def PolicySnapshot.mass (snapshot : PolicySnapshot count) (action : Action count.word.toNat) :
    SwiftTd.ExploreRate :=
  SwiftTd.ExploreRate.project (snapshot.probabilities.get action)

/-- Tree-backup error of the completed transition against the frozen policy's
expected value: `r + γ Σ_a π(a|s′) q(s′, a) − q(s, a)`, in the exact add, multiply,
subtract order. -/
def Controller.backupError {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat) (snapshot : PolicySnapshot count)
    (reward : Binary32) : Binary32 :=
  (reward.add (config.rule.gamma.mul snapshot.expected)).sub controller.vOld

/-- Tree-backup credit for an action the frozen policy did not draw. Precup, Sutton
& Singh, ICML (2000), §4, Algorithm 2: the error bootstraps from the policy's
expected value, `δ = r + γ Σ_a π(a|s′) q(s′, a) − q(s, a)`, and earlier traces decay
by `γλ π(a′|s′)` for the action `a′` taken at `s′`. Acorn's π is the frozen policy's
nominal ε-greedy mass and the sum is `expected`. The correction is a probability by
type; no probability of the selecting policy enters. A taken action outside the
candidates multiplies earlier traces by ε over the action count, and the source's
experimental normalization by the largest mass (p. 5) is not applied. -/
def Controller.backupStep {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (action : Action count.word.toNat) (reward : Binary32) :
    Controller config dimension count.word.toNat :=
  controller.creditStep features action (snapshot.values.get action)
    (controller.backupError snapshot reward)
    (controller.traceDecay.mul (snapshot.mass action).value)

/-- The tree-backup trace correction is a stored probability, in [0, 1], for every
snapshot, including raw nonfinite value words. -/
theorem PolicySnapshot.mass_bounded (snapshot : PolicySnapshot count)
    (action : Action count.word.toNat) :
    SwiftTd.exploreRange.Contains (snapshot.mass action).value := (snapshot.mass action).legal

/-- Tree-backup credit lags the taken action's frozen value, as the on-policy update does. -/
theorem Controller.backupStep_lag {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features : SwiftTd.ActiveSet dimension) (snapshot : PolicySnapshot count)
    (action : Action count.word.toNat) (reward : Binary32) :
    (controller.backupStep features snapshot action reward).vOld = snapshot.values.get action := by
  rw [Controller.backupStep, Controller.creditStep_eq]

end Acorn.Features
