import AcornVerif.CurrentTemporal
import AcornVerif.CurrentConstants
import AcornVerif.CurrentOrder
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace AcornVerif.TemporalSupport
open Acorn Acorn.Features Acorn.Handcrafted

variable {Ω : Type} [Fintype Ω] {interface : Interface} {actions : Word.Count}

structure IncomingLaw (Ω : Type) [Fintype Ω] where
  weight : Ω → ℝ
  nonnegative : ∀ sample, 0 ≤ weight sample
  total : ∑ sample, weight sample = 1
  state : Ω → Rng.Xoshiro256

noncomputable def mass (law : IncomingLaw Ω) (event : Ω → Prop) : ℝ :=
  by classical exact ∑ sample, if event sample then law.weight sample else 0

theorem mass_partition (law : IncomingLaw Ω) (event branch : Ω → Prop) :
    mass law event = mass law (fun sample => event sample ∧ branch sample) +
      mass law (fun sample => event sample ∧ ¬ branch sample) := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sample _
  by_cases h : event sample <;> by_cases b : branch sample <;> simp [h, b]

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

def acts (result : Option (TemporalDecision actions)) (action : Action actions.word.toNat) : Prop :=
  ∃ decision, result = some decision ∧ decision.action = action

def follows (result : Option (TemporalDecision actions)) (event : TemporalDecision actions → Prop) :
    Prop :=
  ∃ decision, result = some decision ∧ event decision

def outcomes {profile : FeatureProfile} {config : Features.Config} {criterion : Criterion}
    {dimension : Dimension} (law : IncomingLaw Ω)
    (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface)
    (reward : Binary32) (goal : Bool) : Ω → Option (TemporalDecision interface.actions) := fun
    sample =>
  let state := { state with runtime := { state.runtime with
    references := { state.runtime.references with rng := law.state sample } } }
  (state.select planning features obs.declared reward goal).map Prod.snd

def optionSource : TemporalSource → Prop
  | .option _ => True
  | .primitive | .explorationStart | .explorationContinuation => False

theorem action_composition (law : IncomingLaw Ω) (run : Ω → Option (TemporalDecision actions))
    (action : Action actions.word.toNat) :
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

def interrupted (decision : TemporalDecision actions) : Prop :=
  ∃ ending, decision.ended = some ending ∧ ending.reason = .interrupted

theorem interruption_composition (law : IncomingLaw Ω) (run : Ω → Option (TemporalDecision actions))
    (action : Action actions.word.toNat) :
    mass law (fun sample => acts (run sample) action) =
      mass law (fun sample => acts (run sample) action ∧ follows (run sample) interrupted) +
      mass law (fun sample => acts (run sample) action ∧ ¬ follows (run sample) interrupted) :=
  mass_partition law _ _

theorem boundary_support (law : IncomingLaw Ω) (run : Ω → Option (TemporalDecision actions))
    (action : Action actions.word.toNat)
    (positive : 0 < mass law (fun sample => acts (run sample) action ∧
      follows (run sample) (fun d => d.source = .explorationStart))) :
    0 < mass law (fun sample => acts (run sample) action) :=
  lt_of_lt_of_le positive (mass_mono law _ _ fun _ h => h.1)

theorem served_other_mass_zero {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension} (law : IncomingLaw Ω)
    (state : TemporalControl interface profile config criterion dimension)
    (planning : PlanningSelection)
    (features : SwiftTd.ActiveSet dimension) (obs : Frame interface)
    (reward : Binary32) (goal : Bool)
    (committed : CommittedRun interface.actions (profile.mode != .frozen))
    (phase : state.runtime.references.phase = .exploring committed)
    (remaining : 0 < committed.run.remaining.val) (action : Action interface.actions.word.toNat)
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
        planning features obs.declared reward goal with
    | none => simp [selected] at returned
    | some result =>
      have exactAction := CurrentTemporal.served_preempts
        ({ state with runtime := { state.runtime with
          references := { state.runtime.references with rng := law.state sample } } })
        (modelOperations criterion dimension) (planningBoundary planning) features
        obs.declared reward goal committed phase remaining result selected
      simp only [selected, Option.map_some, Option.some.injEq] at returned
      subst decision
      exact other (chosen.symm.trans exactAction.1)
  simp [absent]

section DeclaredBranch
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder

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

theorem branch_exact (rng : Rng.Xoshiro256) (rate : SwiftTd.ExploreRate) :
    rng.nextF64.1.less (Conversion.widen rate.value) =
      decide (((rng.next.1 >>> 11).toNat : ℚ) * (2 : ℚ) ^ (-53 : Int) <
        numerical32 rate.value) := by
  have finite : rng.nextF64.1.Finite :=
    CurrentFloat.fraction_finite (Rng.Fraction53.ofWord rng.next.1)
  rw [numerical64_less _ _ finite (Conversion.widen_finite _ rate.legal.1),
    numerical_widen_exact _ rate.legal.1, nextF64_numerical]

theorem declared_branch (rng : Rng.Xoshiro256) :
    rng.nextF64.1.less (Conversion.widen Handcrafted.declaredRate.value) =
      decide ((rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) := by
  rw [branch_exact, CurrentConstants.explore_rate_value, decide_eq_decide, zpow_neg,
    zpow_ofNat, ← div_eq_mul_inv, div_lt_iff₀ (by positivity)]
  have scaled : ModelConstants.exploreRate * 2 ^ 53 = ((10737418 * 2 ^ 23 : ℕ) : ℚ) := by
    norm_num [ModelConstants.exploreRate]
  rw [scaled, Nat.cast_lt]

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

theorem declared_branch_mass :
    ((10737418 * 2 ^ 34 : ℕ) : ℚ) / 2 ^ 64 = ModelConstants.exploreRate := by
  norm_num [ModelConstants.exploreRate]

theorem declared_draw_explored {count : Word.Count} (snapshot : PolicySnapshot count)
    (declared : snapshot.epsilon = Handcrafted.declaredRate) (rng : Rng.Xoshiro256) :
    (snapshot.draw rng).1.explored = decide ((rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) := by
  change rng.nextF64.1.less (Conversion.widen snapshot.epsilon.value) = _
  rw [declared, declared_branch]

theorem declared_persistent_explored {count : Word.Count} (snapshot : PolicySnapshot count)
    (declared : snapshot.epsilon = Handcrafted.declaredRate) (rng : Rng.Xoshiro256) :
    (snapshot.drawPersistent rng).1.explored =
      decide ((rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) := by
  rw [← declared_branch]
  cases branch : rng.nextF64.1.less (Conversion.widen Handcrafted.declaredRate.value) <;>
    simp [PolicySnapshot.drawPersistent_def, beginExploration, declared, branch]

theorem select_declared {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension}
    (state next : TemporalControl interface profile config criterion dimension)
    (declared : profile.rate = .declared)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (potentials : DeclaredPotentials)
    (reward : Binary32) (goal : Bool) (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features potentials reward goal =
      some (next, decision)) :
    CurrentTemporal.Served state next decision ∨
      ∃ (snapshot : PolicySnapshot interface.actions) (rng : Rng.Xoshiro256),
        CurrentTemporal.Handed state decision rng ∧
          CurrentTemporal.Drawn next decision snapshot rng ∧
          snapshot.epsilon = Handcrafted.declaredRate ∧
          decision.explored = decide ((rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) := by
  rcases CurrentTemporal.select_persistent state next models plan features potentials reward
    goal decision executed with served | ⟨origin, ⟨_, drawn⟩ | ⟨slot, _, drawn⟩, handed⟩
  · exact Or.inl served
  · have epsilon := (origin.declared_rates declared).1
    exact Or.inr ⟨_, _, handed, drawn, epsilon,
      drawn.2.1.trans (declared_persistent_explored _ epsilon _)⟩
  · have epsilon : (CurrentTemporal.optionSnapshot origin slot features).epsilon =
        Handcrafted.declaredRate := (origin.declared_rates declared).2.2 fun _ =>
      (origin.runtime.lifecycle.consumers.skills.get slot).policy.exploreRate
        (count := interface.actions)
    exact Or.inr ⟨_, _, handed, drawn, epsilon,
      drawn.2.1.trans (declared_persistent_explored _ epsilon _)⟩

theorem declared_direct {profile : FeatureProfile} {config : Features.Config}
    {criterion : Criterion} {dimension : Dimension}
    (state next : TemporalControl interface profile config criterion dimension)
    (declared : profile.rate = .declared)
    (models : OptionModelOps criterion dimension)
    (plan : PlanBoundary interface.actions config criterion dimension interface.layout)
    (features : SwiftTd.ActiveSet dimension) (potentials : DeclaredPotentials)
    (reward : Binary32) (goal : Bool) (decision : TemporalDecision interface.actions)
    (executed : state.selectWithOperations models plan features potentials reward goal =
      some (next, decision))
    (unserved : decision.source ≠ .explorationContinuation)
    (undrawn : decision.metaDecision = none) :
    decision.explored =
      decide ((state.runtime.references.rng.next.1 >>> 11).toNat < 10737418 * 2 ^ 23) := by
  rcases select_declared state next declared models plan features potentials reward goal
    decision executed with ⟨_, _, _, _, source, _⟩ | ⟨snapshot, rng, handed, _, _, explored⟩
  · exact absurd source unserved
  · rcases handed with ⟨_, same⟩ | ⟨metaSnapshot, recorded, _⟩
    · rw [explored, same]
    · rw [undrawn] at recorded
      cases recorded

end DeclaredBranch

end AcornVerif.TemporalSupport
