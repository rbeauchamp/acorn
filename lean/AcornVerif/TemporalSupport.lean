/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import AcornVerif.CurrentTemporal

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
  · simp only [hs, if_false]
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
option contribution includes any actual interruption and re-selection. -/
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
    (reward : Binary32) (goal : Bool) (run : ExploratoryRun primitiveCount)
    (phase : state.runtime.references.phase = .exploring run)
    (remaining : 0 < run.remaining.val) (action : Action primitiveCount.word.toNat)
    (other : action ≠ run.action) :
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
        (spatialPotentials obs) reward goal run phase remaining result selected
      simp only [selected, Option.map_some, Option.some.injEq] at returned
      subst decision
      exact other (chosen.symm.trans exactAction.1)
  simp [absent]

end AcornVerif.TemporalSupport
