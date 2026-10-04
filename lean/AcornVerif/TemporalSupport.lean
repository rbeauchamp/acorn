/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentTemporal
import AcornVerif.CurrentConstants
import AcornVerif.CurrentOrder
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Conditional action laws of actual temporal dispatch

The generator is deterministic. A probability statement therefore requires a
law on its incoming state. These symbolic finite sums push an arbitrary
nonnegative normalized law through the actual selector; no independence of
successive xoshiro words, uniform reservoir ties, or exact nominal epsilon is
assumed. No finite sum is evaluated by these proofs or by the agent.

Dabney, Ostrovski & Barreto, *Temporally-Extended ε-Greedy Exploration*, ICLR
(2021), arXiv:2006.01782v1 (2020), §4.2, describes the action-repeat option.
A served step is conditionally deterministic. The total-law decomposition
includes persistence, interruption and new option selection; a positive
primitive-boundary contribution supplies a floor only under its stated law.

Every exploration branch compares the first source word's 53-bit fraction with
the stored rate as exact rational order (`branch_exact`). At D6's declared rate
it explores for exactly `10737418 · 2^34` of the `2^64` first words
(`declared_branch_card`): the rate's exact binary32 value under a uniform
first-word hypothesis, which a deterministic xoshiro prefix does not supply.

`select_declared` carries that branch to the behaviour as a whole: under the declared
policy, every decision the executed selection returns is a served step of a committed
run or one persistent draw at D6's rate, whichever layer selected the action
(Algorithm 1 of the same source, PDF p. 14).
-/
namespace AcornVerif.TemporalSupport
open Acorn Acorn.Features Acorn.Handcrafted

variable {Ω : Type} [Fintype Ω]

/-- A probability law on incoming generator states, stated rather than inferred
from a pseudorandom implementation. The index may represent any finite support. -/
structure IncomingLaw (Ω : Type) [Fintype Ω] where
  /-- Nonnegative incoming-state weights. -/
  weight : Ω → ℝ
  /-- No negative probability mass. -/
  nonnegative : ∀ sample, 0 ≤ weight sample
  /-- Total probability one. -/
  total : ∑ sample, weight sample = 1
  /-- Actual generator state associated with each support element. -/
  state : Ω → Rng.Xoshiro256

/-- Exact pushforward event mass; this is a mathematical definition only. -/
noncomputable def mass (law : IncomingLaw Ω) (event : Ω → Prop) : ℝ :=
  by classical exact ∑ sample, if event sample then law.weight sample else 0

/-- Partition is total probability, without independence or uniform-draw hypotheses. -/
theorem mass_partition (law : IncomingLaw Ω) (event branch : Ω → Prop) :
    mass law event = mass law (fun sample => event sample ∧ branch sample) +
      mass law (fun sample => event sample ∧ ¬ branch sample) := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sample _
  by_cases h : event sample <;> by_cases b : branch sample <;> simp [h, b]

/-- A subevent cannot have more mass than the action event containing it. -/
theorem mass_mono (law : IncomingLaw Ω) (small large : Ω → Prop)
    (contained : ∀ sample, small sample → large sample) : mass law small ≤ mass law large := by
  classical
  apply Finset.sum_le_sum
  intro sample _
  by_cases hs : small sample
  · simp [hs, contained sample hs]
  · simp only [hs, ite_false]
    split
    · exact law.nonnegative sample
    · exact le_rfl

/-- A singleton output predicate never invents an action for a refused transition. -/
def acts (result : Option TemporalDecision) (action : Action primitiveCount.word.toNat) : Prop :=
  ∃ decision, result = some decision ∧ decision.action = action

/-- Inspect a branch only for an actual returned decision. -/
def follows (result : Option TemporalDecision) (event : TemporalDecision → Prop) : Prop :=
  ∃ decision, result = some decision ∧ event decision

/-- Current policy selection under the supplied law, with every other state and
input held fixed. The full RNG state feeds all conditional subsequent draws. -/
def outcomes {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} (law : IncomingLaw Ω)
    (state : TemporalControl profile config criterion dimension)
    (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation)
    (reward : Binary32) (goal : Bool) : Ω → Option TemporalDecision := fun sample =>
  let state := { state with runtime := { state.runtime with
    references := { state.runtime.references with rng := law.state sample } } }
  (state.select planning features (spatialPotentials obs) reward goal).map Prod.snd

/-- Classify option actions without interpreting the slot as host vocabulary. -/
def optionSource : TemporalSource → Prop
  | .option _ => True
  | .primitive | .explorationStart | .explorationContinuation => False

/-- Exact action-mass decomposition into served persistence, option-policy and
fresh primitive contributions. It applies in particular to `outcomes`, whose
option contribution includes any interruption by a stopping estimate and
re-selection; an interruption by a run falls in the served contribution. -/
theorem action_composition (law : IncomingLaw Ω) (run : Ω → Option TemporalDecision)
    (action : Action primitiveCount.word.toNat) :
    mass law (fun sample => acts (run sample) action) =
      mass law (fun sample => acts (run sample) action ∧
        follows (run sample) (fun d => d.source = .explorationContinuation)) +
      mass law (fun sample => acts (run sample) action ∧
        ¬ follows (run sample) (fun d => d.source = .explorationContinuation) ∧
        follows (run sample) (fun d => optionSource d.source)) +
      mass law (fun sample => acts (run sample) action ∧
        ¬ follows (run sample) (fun d => d.source = .explorationContinuation) ∧
        ¬ follows (run sample) (fun d => optionSource d.source)) := by
  let served := fun sample => follows (run sample) (fun d => d.source = .explorationContinuation)
  let option := fun sample => follows (run sample) (fun d => optionSource d.source)
  rw [mass_partition law (fun sample => acts (run sample) action) served]
  rw [mass_partition law (fun sample => acts (run sample) action ∧ ¬ served sample) option]
  simp only [served, option, and_assoc, add_assoc]

/-- Interruption is an observable conditioning event on the actual transition,
not an independent probability multiplied into an unrelated policy model. -/
def interrupted (decision : TemporalDecision) : Prop :=
  ∃ ending, decision.ended = some ending ∧ ending.reason = .interrupted

/-- Conditional terminal and continuing paths partition the same actual action law. -/
theorem interruption_composition (law : IncomingLaw Ω) (run : Ω → Option TemporalDecision)
    (action : Action primitiveCount.word.toNat) :
    mass law (fun sample => acts (run sample) action) =
      mass law (fun sample => acts (run sample) action ∧ follows (run sample) interrupted) +
      mass law (fun sample => acts (run sample) action ∧ ¬ follows (run sample) interrupted) :=
  mass_partition law _ _

/-- A boundary floor is conditional on positive mass reaching that boundary
and drawing this action. It gives no support theorem for served steps. -/
theorem boundary_support (law : IncomingLaw Ω) (run : Ω → Option TemporalDecision)
    (action : Action primitiveCount.word.toNat)
    (positive : 0 < mass law (fun sample => acts (run sample) action ∧
      follows (run sample) (fun d => d.source = .explorationStart))) :
    0 < mass law (fun sample => acts (run sample) action) :=
  lt_of_lt_of_le positive (mass_mono law _ _ fun _ h => h.1)

/-- Actual persistent dispatch has zero mass on every other action under any
incoming RNG law, even with arbitrary goal feedback and planning selections. -/
theorem served_other_mass_zero {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} (law : IncomingLaw Ω)
    (state : TemporalControl profile config criterion dimension)
    (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (obs : Host.Observation)
    (reward : Binary32) (goal : Bool) (committed : CommittedRun (profile.mode != .frozen))
    (phase : state.runtime.references.phase = .exploring committed)
    (remaining : 0 < committed.run.remaining.val) (action : Action primitiveCount.word.toNat)
    (other : action ≠ committed.run.action) :
    mass law (fun sample => acts (outcomes law state planning features obs reward goal sample)
      action) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro sample _
  have absent : ¬ acts (outcomes law state planning features obs reward goal sample) action := by
    intro ⟨decision, returned, chosen⟩
    unfold outcomes at returned
    cases selected : ({ state with runtime := { state.runtime with
        references := { state.runtime.references with rng := law.state sample } } }).select
        planning features (spatialPotentials obs) reward goal with
    | none => simp [selected] at returned
    | some result =>
      have exactAction := CurrentTemporal.served_preempts
        ({ state with runtime := { state.runtime with
          references := { state.runtime.references with rng := law.state sample } } })
        (modelOperations criterion dimension) (planningBoundary planning) features
        (spatialPotentials obs) reward goal committed phase remaining result selected
      simp only [selected, Option.map_some, Option.some.injEq] at returned
      subst decision
      exact other (chosen.symm.trans exactAction.1)
  simp [absent]

section DeclaredBranch
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder

/-- Every actual floating draw is its first word's 53-bit numerator scaled by
`2^-53`, read as a nonnegative dyadic rational. -/
theorem nextF64_numerical (rng : Rng.Xoshiro256) :
    numerical64 rng.nextF64.1 = ((rng.next.1 >>> 11).toNat : ℚ) * (2 : ℚ) ^ (-53 : Int) := by
  have finite : rng.nextF64.1.Finite :=
    CurrentFloat.fraction_finite (Rng.Fraction53.ofWord rng.next.1)
  have below := CurrentFloat.nextF64_word_lt_one rng
  have unsigned : (rng.nextF64.1.bits &&& 0x8000000000000000 != 0) = false := by
    have mask := CurrentFloat.word64_sign_exact rng.nextF64.1.bits
    have zero : rng.nextF64.1.bits &&& 0x8000000000000000 = 0 := by
      apply UInt64.toNat.inj
      rw [mask, Nat.div_eq_of_lt (by omega)]
      rfl
    simp [zero]
  rw [numerical64_units _ finite, model_word64_sign, unsigned, CurrentFloat.nextF64_value_exact]
  simp only [Bool.false_eq_true, ↓reduceIte, signCoefficient, one_mul, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat]
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  norm_num

/-- The branch comparison of `PolicySnapshot.draw` and `beginExploration` is
exact rational order between the first word's 53-bit fraction and the stored
rate's binary32 value, for every generator state and every legal rate. -/
theorem branch_exact (rng : Rng.Xoshiro256) (rate : SwiftTd.ExploreRate) :
    rng.nextF64.1.less (Conversion.widen rate.value) =
      decide (((rng.next.1 >>> 11).toNat : ℚ) * (2 : ℚ) ^ (-53 : Int) <
        numerical32 rate.value) := by
  have finite : rng.nextF64.1.Finite :=
    CurrentFloat.fraction_finite (Rng.Fraction53.ofWord rng.next.1)
  rw [numerical64_less _ _ finite (Conversion.widen_finite _ rate.legal.1),
    numerical_widen_exact _ rate.legal.1, nextF64_numerical]

/-- At the declared D6 rate the branch explores exactly when the first word's
53-bit numerator is below `10737418 · 2^23`, the rate's exact value times `2^53`. -/
theorem declared_branch (rng : Rng.Xoshiro256) :
    rng.nextF64.1.less (Conversion.widen Handcrafted.declaredRate.value) =
      decide ((rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) := by
  rw [branch_exact, CurrentConstants.explore_rate_value, decide_eq_decide, zpow_neg,
    zpow_ofNat, ← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
  have scaled : ModelConstants.exploreRate * 2 ^ 53 = ((10737418 * 2 ^ 23 : ℕ) : ℚ) := by
    norm_num [ModelConstants.exploreRate]
  rw [scaled, Nat.cast_lt]

/-- Exactly `10737418 · 2^34` of the `2^64` first source words take the declared
branch. Counting preimages gives a mass only under a uniform first-word
hypothesis; under it the mass is `ModelConstants.exploreRate` exactly. -/
theorem declared_branch_card :
    ((Finset.range (2 ^ 64)).filter (fun word : ℕ =>
      (word.toUInt64 >>> 11).toNat < 10737418 * 2 ^ 23)).card = 10737418 * 2 ^ 34 := by
  have same : (Finset.range (2 ^ 64)).filter (fun word : ℕ =>
      (word.toUInt64 >>> 11).toNat < 10737418 * 2 ^ 23) = Finset.range (10737418 * 2 ^ 34) := by
    ext word
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨bounded, below⟩
      rw [UInt64.toNat_shiftRight] at below
      change (word % 2 ^ 64) >>> 11 < 10737418 * 2 ^ 23 at below
      rw [Nat.mod_eq_of_lt bounded, Nat.shiftRight_eq_div_pow,
        Nat.div_lt_iff_lt_mul (by positivity)] at below
      omega
    · intro below
      have bounded : word < 2 ^ 64 := by omega
      refine ⟨bounded, ?_⟩
      rw [UInt64.toNat_shiftRight]
      change (word % 2 ^ 64) >>> 11 < 10737418 * 2 ^ 23
      rw [Nat.mod_eq_of_lt bounded, Nat.shiftRight_eq_div_pow,
        Nat.div_lt_iff_lt_mul (by positivity)]
      omega
  rw [same, Finset.card_range]

/-- The first-word count is the declared rate's exact share of `2^64` words. -/
theorem declared_branch_mass :
    ((10737418 * 2 ^ 34 : ℕ) : ℚ) / 2 ^ 64 = ModelConstants.exploreRate := by
  norm_num [ModelConstants.exploreRate]

/-- A plain policy draw at the declared rate, as the meta-controller makes over meta
actions, explores exactly on the declared first-word numerators. -/
theorem declared_draw_explored {count : Word.Count} (snapshot : PolicySnapshot count)
    (declared : snapshot.epsilon = Handcrafted.declaredRate) (rng : Rng.Xoshiro256) :
    (snapshot.draw rng).1.explored = decide ((rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) := by
  change rng.nextF64.1.less (Conversion.widen snapshot.epsilon.value) = _
  rw [declared, declared_branch]

/-- A persistent draw at the declared rate, as primitive control and every executing
option make, begins a run exactly on the same first-word numerators. -/
theorem declared_persistent_explored {count : Word.Count} (snapshot : PolicySnapshot count)
    (declared : snapshot.epsilon = Handcrafted.declaredRate) (rng : Rng.Xoshiro256) :
    (snapshot.drawPersistent rng).1.explored =
      decide ((rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) := by
  rw [← declared_branch]
  cases branch : rng.nextF64.1.less (Conversion.widen Handcrafted.declaredRate.value) <;>
    simp [PolicySnapshot.drawPersistent, beginExploration, declared, branch]

/-- Reach at the declared rate, over the executed selection. Under the declared rate
policy, every decision the selection returns is a served step of a committed run, or
the outcome of one persistent draw at D6's rate: it explores exactly on the declared
first-word numerators of the generator state it was drawn at, whichever layer selected
the action. The count of those numerators is `declared_branch_card`; it is a probability
only under a uniform first-word hypothesis, which the deterministic generator does not
supply. -/
theorem select_declared {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension}
    (state next : TemporalControl profile config criterion dimension)
    (declared : profile.rate = .declared)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary config criterion dimension demonLayout)
    (features : SwiftTd.ActiveSet dimension) (potentials : DeclaredPotentials)
    (reward : Binary32) (goal : Bool) (decision : TemporalDecision)
    (executed : state.selectWithOperations models plan features potentials reward goal =
      some (next, decision)) :
    decision.source = .explorationContinuation ∨
      ∃ (snapshot : PolicySnapshot primitiveCount) (rng : Rng.Xoshiro256),
        CurrentTemporal.Drawn next decision snapshot rng ∧
          snapshot.epsilon = Handcrafted.declaredRate ∧
          decision.explored = decide ((rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) := by
  rcases CurrentTemporal.select_persistent state next models plan features potentials reward
    goal decision executed with served | ⟨origin, ⟨_, drawn⟩ | ⟨slot, _, drawn⟩⟩
  · exact Or.inl served
  · have epsilon := (origin.declared_rates declared).1
    exact Or.inr ⟨_, _, drawn, epsilon,
      drawn.2.1.trans (declared_persistent_explored _ epsilon _)⟩
  · have epsilon : (CurrentTemporal.optionSnapshot origin slot features).epsilon =
        Handcrafted.declaredRate := (origin.declared_rates declared).2.2 fun _ =>
      (origin.runtime.lifecycle.consumers.skills.get slot).policy.exploreRate
        (count := primitiveCount)
    exact Or.inr ⟨_, _, drawn, epsilon,
      drawn.2.1.trans (declared_persistent_explored _ epsilon _)⟩

end DeclaredBranch

end AcornVerif.TemporalSupport
