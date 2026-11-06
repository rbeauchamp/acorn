/-
Copyright (c) 2026 acorn contributors. All rights reserved.
Released under the MIT license as described in the repository LICENSE.
Authors: acorn contributors
-/
import Acorn.Handcrafted.PredictionControl
import AcornVerif.CurrentBackupBounds
import AcornVerif.CurrentFeatureConsumers
import AcornVerif.CurrentPrediction

/-!
# Contracts of the executing prediction/control composition

These theorems reuse the actual numeric learner and its admitted schedule.
Off-policy credit (Precup, Sutton & Singh, ICML (2000), §4, Algorithm 2) and
stopping credit pass raw words to the same learner entries.
The action update is Javed & Sutton, *Swift-Sarsa*, arXiv:2507.19539v1 (2025),
Algorithm 1 / equation (4), with the PAR-2 meta-gradient adaptation owned by
`MetaGradient`. Each theorem identifies its machine-word or ideal-real domain.

The last section characterizes the greedy draw's near-maximum candidates over the executed
binary32 words: a gap above the tie window leaves one action, and zero weights outside an anchor
set leave the anchor's candidates.
-/
namespace AcornVerif.CurrentControl
open Acorn Acorn.Features AcornVerif.CurrentFeatureConsumers AcornVerif.CurrentLearner

variable {config : Acorn.Config} {dimension : Dimension} {actions : Nat}

/-- Every live controller row carries the actual learner's support, pruning
reference, unique-eligibility and readiness invariants. -/
theorem controller_schedule (controller : Controller config dimension actions)
    (action : Action actions) :
    ScheduleInv (controller.learners.get action).state
      (controller.learners.get action).phase :=
  managed_schedule (controller.learners.get action)

/-- Complete shared-error execution preserves stored weight/beta legality and
eligibility capacity, for arbitrary raw reward, bootstrap and decay words. -/
theorem values_step_legal (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action observed : Action actions) (reward bootstrap decay : Binary32)
    (index : FeatIdx dimension) :
    let next := controller.valuesStep features values action reward bootstrap decay
    let learner := next.learners.get observed
    config.rule.domain.range.Contains (learner.state.weights.get index).value ∧
    learner.state.rails.range.Contains (learner.state.beta.get index).value ∧
    learner.state.eligibleCount ≤ dimension.capacity := by
  dsimp only
  exact ⟨weight_legal _, (by exact Bounded32.legal _), managed_capacity _⟩

/-- The shared-error kernel preserves stored weight/beta legality and eligibility
capacity for arbitrary raw lag, error and decay words; tree-backup credit and the
zero-error start of an off-policy trajectory are instances. -/
theorem credit_step_legal (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action observed : Action actions)
    (lag delta decay : Binary32) (index : FeatIdx dimension) :
    let next := controller.creditStep features action lag delta decay
    let learner := next.learners.get observed
    config.rule.domain.range.Contains (learner.state.weights.get index).value ∧
    learner.state.rails.range.Contains (learner.state.beta.get index).value ∧
    learner.state.eligibleCount ≤ dimension.capacity := by
  dsimp only
  exact ⟨weight_legal _, (by exact Bounded32.legal _), managed_capacity _⟩

/-- Stopping credit preserves the same stored legality and eligibility capacity. -/
theorem stop_step_legal (controller : Controller config dimension actions)
    (delta : Binary32) (observed : Action actions) (index : FeatIdx dimension) :
    let learner := (controller.stopStep delta).learners.get observed
    config.rule.domain.range.Contains (learner.state.weights.get index).value ∧
    learner.state.rails.range.Contains (learner.state.beta.get index).value ∧
    learner.state.eligibleCount ≤ dimension.capacity := by
  dsimp only
  exact ⟨weight_legal _, (by exact Bounded32.legal _), managed_capacity _⟩

/-- At zero trace decay a visited finite trace is pruned, for every managed learner
and every error and accumulator word, so the release after stopping credit has
nothing left to visit when the eligible traces are finite. -/
theorem stop_prunes (learner : Managed config dimension) (idx : FeatIdx dimension)
    (delta vDelta : Binary32) (finite : (learner.state.transient.z.get idx).value.Finite) :
    (learner.state.firstLoopElement idx delta vDelta .zero).2 = true := by
  have zero := zero_decay_trace _ finite
  have trace : ((learner.state.firstLoopElement idx delta vDelta .zero).1.transient.z.get
      idx).value = (learner.state.transient.z.get idx).value.mul .zero := by
    simp only [NumericState.firstLoopElement, vector_get, Vector.getElem_set_self]
  cases retained : (learner.state.firstLoopElement idx delta vDelta .zero).2 with
  | true => rfl
  | false =>
    have kept := first_element_retained_nonzero learner.state idx delta vDelta .zero
      (managed_schedule learner).1.2 retained
    rw [trace, zero] at kept
    contradiction

/-- Work bound at a stop: stopping credit leaves every action learner nothing
eligible, for every state and every trace word, because its last entry releases
the list structurally. The start that follows a stop therefore visits no earlier
trace. -/
theorem stop_step_empty (controller : Controller config dimension actions) (delta : Binary32)
    (action : Action actions) :
    ((controller.stopStep delta).learners.get action).state.eligibleCount = 0 := by
  simp only [Controller.stopStep_eq, vector_get, Vector.getElem_map]
  rfl

/-- A closed span leaves every action learner nothing eligible, and the first loop of
whatever credit comes next is the identity on it, for every error, accumulator and decay
word: no reward delivered after the close reaches an action credited before it. -/
theorem close_step_idle (controller : Controller config dimension actions)
    (reward continuation : Binary32) (duration : UInt32) (action : Action actions)
    (delta vDelta decay : Binary32) :
    ((controller.closeStep reward continuation duration).learners.get action).state.eligibleCount
        = 0 ∧
      ((controller.closeStep reward continuation duration).learners.get
        action).state.learnFirstLoop config delta vDelta decay =
        ((controller.closeStep reward continuation duration).learners.get action).state := by
  rw [Controller.closeStep_def]
  refine ⟨stop_step_empty _ _ action, ?_⟩
  simp only [Controller.stopStep_eq, vector_get, Vector.getElem_map]
  exact release_idle _ delta vDelta decay

/-- A release leaves every action learner nothing eligible and with its weights,
so the first loops of the start that follows read no trace and credit no earlier
transition (`release_idle`). -/
theorem release_rows (controller : Controller config dimension actions) (action : Action actions)
    (idx : FeatIdx dimension) :
    (controller.release.learners.get action).state.eligibleCount = 0 ∧
      (controller.release.learners.get action).state.weights.get idx =
        (controller.learners.get action).state.weights.get idx := by
  simp only [Controller.release_def, vector_get, Vector.getElem_map]
  exact ⟨rfl, (release_knowledge _ idx).1⟩

/-- The selected row executes first-loop credit then precisely one second loop. -/
theorem selected_row (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action : Action actions) (reward bootstrap decay : Binary32) :
    ((controller.valuesStep features values action reward bootstrap decay).learners.get
      action).state =
      (((controller.learners.get action).credit
        ((reward.add (bootstrap.mul (values.get action))).sub controller.vOld)
        controller.vDelta decay controller.restartPending).val.state.learnSecondLoop
          config features .zero).1 := by
  simp [Controller.valuesStep_def, Controller.creditStep_eq, Vector.get, Fin.cast]

/-- Every unselected row receives the same first-loop error, without a second loop. -/
theorem unselected_row (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (values : Vector Binary32 actions)
    (action other : Action actions) (different : other ≠ action)
    (reward bootstrap decay : Binary32) :
    ((controller.valuesStep features values action reward bootstrap decay).learners.get
      other).state =
      ((controller.learners.get other).credit
        ((reward.add (bootstrap.mul (values.get action))).sub controller.vOld)
        controller.vDelta decay controller.restartPending).val.state := by
  have indices : other.val ≠ action.val := fun h => different (Fin.ext h)
  simp [Controller.valuesStep_def, Controller.creditStep_eq, Vector.get, Fin.cast, Ne.symm indices]

/-- Terminal closeout clears all trajectory registers in every action row. -/
theorem terminal_clears (controller : Controller config dimension actions)
    (reward : Binary32)
    (action : Action actions) :
    ((controller.terminal reward).learners.get action).state.transient =
      TransientState.zero dimension := by
  simp [Controller.terminal_eq, Controller.clear_def, Vector.get, Managed.apply_state,
    SwiftTd.Entry.apply_def, NumericState.clearTransient_def]

/-- Controller observations are finite because they sum the actual refined weights,
not because the output is clamped or a separately written prediction model is assumed. -/
theorem prediction_finite (controller : Controller config dimension actions)
    (features : SwiftTd.ActiveSet dimension) (action : Action actions) :
    ((controller.predictAll features).get action).Finite := by
  have result := CurrentPrediction.legal_weight_sum_bound config.rule
    (features.indices.map fun idx => ((controller.learners.get action).state.weights.get idx))
  simpa [Controller.predictAll_def, Vector.get, NumericState.linearPrediction_eq_sumFrom,
    List.map_map, Fin.cast, Function.comp_def] using result.1

/-- An actual greedy draw returns a threshold candidate whenever one exists;
otherwise its exact raw-domain behavior is the first-action fallback. -/
theorem greedy_support {count : Word.Count} (snapshot : PolicySnapshot count)
    (rng : Rng.Xoshiro256) :
    if snapshot.candidates = [] then (snapshot.greedy rng).1 = firstAction count
    else (snapshot.greedy rng).1 ∈ snapshot.candidates := by
  cases h : snapshot.candidates with
  | nil => simp [PolicySnapshot.greedy_def, h, reservoir_nil]
  | cons action rest =>
    simpa [PolicySnapshot.greedy_def, h] using
      reservoir_nonempty action rest (firstAction count) rng

/-- Every finite sequence of actual local control transitions retains the receiver's
same configuration, legal knowledge and resource scheduling; no replay is stored. -/
theorem finite_prefix_schedule (initial : Controller config dimension actions)
    (inputs : List (SwiftTd.ActiveSet dimension × Action actions × Binary32))
    (action : Action actions) :
    let final := inputs.foldl
      (fun state input => (state.step input.1 input.2.1 input.2.2).1) initial
    ScheduleInv (final.learners.get action).state (final.learners.get action).phase := by
  exact controller_schedule _ action

/-- Every actual bank transition preserves the current learner's resource bound
at every heterogeneous reader, independently of its signal discount. -/
theorem demon_step_capacity {discounts : List Discount} (bank : DemonBank dimension discounts)
    (features : SwiftTd.ActiveSet dimension) (rewards : Cumulants discounts)
    (reader : PackedLearner dimension)
    (_member : reader ∈ (bank.step features rewards).bank.readers) :
    reader.2.state.eligibleCount ≤ dimension.capacity := managed_capacity reader.2

/-! ## A bias on a few slots and the greedy choice

The greedy draw keeps the actions whose frozen value is within the tie window of the ordered
maximum (`PolicySnapshot.candidates`). The theorems below characterize that list over the executed
binary32 words, NaN, signed zeros and rounding included. A finite value more than the window above
every other is the one candidate (`candidates_of_gap`). Weights that are zero words on the active
slots outside an anchor set leave the anchor's candidates (`candidates_of_resting`). Each takes the
values or weights as a hypothesis and says nothing about whether a run reaches them. -/

section Bias
open Float.Model (Format UnpackedFloat)
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentOperations
  AcornVerif.CurrentBackupBounds

/-- The magnitude field is the stored word modulo `2^31`, the word without its sign bit. -/
theorem magnitude_mod (word : Binary32) : word.magnitude = word.bits.toNat % 2 ^ 31 := by
  unfold Binary32.magnitude
  rw [UInt32.toNat_and]
  exact Nat.and_two_pow_sub_one_eq_mod _ 31

/-- A finite word is not a NaN. -/
theorem finite_not_isNaN {word : Binary32} (finite : word.Finite) : ¬word.IsNaN := by
  rw [← Binary32.isNaN_iff, Binary32.finite_not_nan word finite]
  decide

/-- A zero word is positive or negative zero. -/
theorem zero_cases (word : Binary32) (zero : word.isZero = true) :
    word = ⟨0⟩ ∨ word = ⟨0x80000000⟩ := by
  have key := zero_key word zero
  have bound := word.bits.toNat_lt
  have field := magnitude_mod word
  rw [Binary32.key_eq_negative] at key
  have none : word.magnitude = 0 := by split at key <;> omega
  obtain ⟨bits⟩ := word
  change bits.toNat < 2 ^ 32 at bound
  change _ = bits.toNat % 2 ^ 31 at field
  have cases : bits.toNat = 0 ∨ bits.toNat = 2 ^ 31 := by omega
  rcases cases with low | high
  · exact Or.inl (congrArg Binary32.mk (UInt32.toNat_inj.mp low))
  · exact Or.inr (congrArg Binary32.mk (UInt32.toNat_inj.mp high))

/-- A zero word is finite. -/
theorem zero_finite (word : Binary32) (zero : word.isZero = true) : word.Finite := by
  rcases zero_cases word zero with rfl | rfl <;> decide

/-- Two words with one key are one word, or both zero words. -/
theorem key_inj (left right : Binary32) (same : left.key = right.key) :
    left = right ∨ (left.isZero = true ∧ right.isZero = true) := by
  by_cases zero : left.key = 0
  · refine Or.inr ⟨?_, ?_⟩
    · rw [Binary32.isZero_eq_key]; exact decide_eq_true zero
    · rw [Binary32.isZero_eq_key]; exact decide_eq_true (same ▸ zero)
  · refine Or.inl ?_
    have lm := magnitude_mod left
    have rm := magnitude_mod right
    have lb := left.bits.toNat_lt
    have rb := right.bits.toNat_lt
    unfold Binary32.key Binary32.Negative at same zero
    obtain ⟨lbits⟩ := left
    obtain ⟨rbits⟩ := right
    change lbits.toNat < 2 ^ 32 at lb
    change rbits.toNat < 2 ^ 32 at rb
    have equal : lbits.toNat = rbits.toNat := by
      dsimp only at same zero lm rm
      split_ifs at same zero <;> omega
    exact congrArg Binary32.mk (UInt32.toNat_inj.mp equal)

/-- Both zero words less the tie window give one word, by a closed computation. -/
theorem zero_sub_tie (left right : Binary32) (lz : left.isZero = true)
    (rz : right.isZero = true) : left.sub tieWindow = right.sub tieWindow := by
  rcases zero_cases left lz with rfl | rfl <;> rcases zero_cases right rz with rfl | rfl <;>
    decide +kernel

/-- A normalized model value below `2^128` in magnitude passes the packing guard, so it packs to a
finite binary32 word. -/
theorem fits_of_abs_lt (value : UnpackedFloat) (normal : ModelNormalized Format.binary32 value)
    (bound : |unpackedValue value| < (2 : ℚ) ^ (128 : Int)) :
    ModelFits Format.binary32 value := by
  cases value with
  | notANumber => exact normal.elim
  | infinity sign => exact normal.elim
  | zero sign => trivial
  | finite sign mantissa exponent positive =>
    obtain ⟨_, low, scale⟩ := normal
    have least : Format.binary32.minExponent = -149 := by decide
    have width : Format.binary32.mantissaBitsWithoutImplicit = 23 := by decide
    rw [least] at low scale
    rw [width] at scale
    have exponentBound : exponent ≤ 104 := by
      rcases scale with floor | large
      · omega
      · rw [model_finite_abs] at bound
        have hm : (2 : ℚ) ^ (23 : Int) ≤ mantissa := by
          have large' : 8388608 ≤ mantissa := by simpa using large
          rw [show (2 : ℚ) ^ (23 : Int) = 8388608 by norm_num]
          exact_mod_cast large'
        have hp : (0 : ℚ) < (2 : ℚ) ^ exponent := zpow_pos (by norm_num) _
        have power : (2 : ℚ) ^ (exponent + 23) < (2 : ℚ) ^ (128 : Int) := by
          rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
          calc (2 : ℚ) ^ exponent * (2 : ℚ) ^ (23 : Int)
              = (2 : ℚ) ^ (23 : Int) * (2 : ℚ) ^ exponent := mul_comm _ _
            _ ≤ mantissa * (2 : ℚ) ^ exponent := mul_le_mul_of_nonneg_right hm hp.le
            _ < (2 : ℚ) ^ (128 : Int) := bound
        have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mp power
        omega
    change (exponent + (127 : Nat) + (23 : Nat)).toNat + 1 < 2 ^ 8
    omega

/-- The tie window's exact value, `8796093 · 2^(-43)`, a little below `10^(-6)`. -/
theorem tie_value : numerical32 tieWindow = 8796093 * (2 : ℚ) ^ (-43 : Int) := by
  change (1 : ℚ) * 8796093 * (2 : ℚ) ^ (-43 : Int) = _
  ring

/-- Every finite word's value is at most the largest finite value, `(2^24 - 1) · 2^104`. -/
theorem below_highest (word : Binary32) (finite : word.Finite) :
    numerical32 word ≤ 16777215 * (2 : ℚ) ^ (104 : Int) := by
  have value : numerical32 (⟨0x7f7fffff⟩ : Binary32) = 16777215 * (2 : ℚ) ^ (104 : Int) := by
    change (1 : ℚ) * 16777215 * (2 : ℚ) ^ (104 : Int) = _
    ring
  rw [← value, numerical32_order _ _ finite (by decide)]
  have top : (⟨0x7f7fffff⟩ : Binary32).key = 0x7f7fffff := by decide
  rw [top, Binary32.key]
  unfold Binary32.Finite at finite
  split <;> omega

/-- Every finite word other than the most negative one has value at least `-(2^24 - 2) · 2^104`,
the next finite value above the most negative. -/
theorem above_lowest (word : Binary32) (finite : word.Finite) (other : word ≠ ⟨0xff7fffff⟩) :
    -16777214 * (2 : ℚ) ^ (104 : Int) ≤ numerical32 word := by
  have value : numerical32 (⟨0xff7ffffe⟩ : Binary32) = -16777214 * (2 : ℚ) ^ (104 : Int) := by
    change (-1 : ℚ) * 16777214 * (2 : ℚ) ^ (104 : Int) = _
    ring
  rw [← value, numerical32_order _ _ (by decide) finite]
  have bottom : (⟨0xff7ffffe⟩ : Binary32).key = -0x7f7ffffe := by decide
  rw [bottom]
  have field := magnitude_mod word
  have bound := word.bits.toNat_lt
  unfold Binary32.Finite at finite
  unfold Binary32.key Binary32.Negative
  obtain ⟨bits⟩ := word
  change bits.toNat < 2 ^ 32 at bound
  dsimp only at field finite ⊢
  have distinct : bits.toNat ≠ 0xff7fffff := fun same =>
    other (congrArg Binary32.mk (UInt32.toNat_inj.mp same))
  split_ifs <;> omega

/-- Subtracting the tie window from a finite word gives a word that is not a NaN and has a key at
most the word's own. The difference is rounded once, never above the word and never past the
finite range; the most negative finite word is the one case a closed computation settles. -/
theorem sub_tie_le (word : Binary32) (finite : word.Finite) :
    ¬(word.sub tieWindow).IsNaN ∧ (word.sub tieWindow).key ≤ word.key := by
  by_cases lowest : word = ⟨0xff7fffff⟩
  · subst lowest
    decide +kernel
  have tieFinite : tieWindow.Finite := by decide
  have ln := (model_unpack_format Format.binary32 (by decide) word.bits.toBitVec
    ((model_decoded32_finite word).mpr finite)).1
  have rn := (model_unpack_format Format.binary32 (by decide) tieWindow.bits.toBitVec
    ((model_decoded32_finite tieWindow).mpr tieFinite)).1
  have low := above_lowest word finite lowest
  have high := below_highest word finite
  have tie := tie_value
  have unit : (0 : ℚ) < (2 : ℚ) ^ (104 : Int) := zpow_pos (by norm_num) _
  have tiePositive : 0 < numerical32 tieWindow := by rw [tie]; positivity
  have tieSmall : numerical32 tieWindow ≤ 1 := by rw [tie]; norm_num
  have scale : (2 : ℚ) ^ (128 : Int) = 16777216 * (2 : ℚ) ^ (104 : Int) := by
    rw [show (128 : Int) = 24 + 104 by norm_num, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    norm_num
  have operation := model_sub_dyadic_local Format.binary32 (decoded32 word)
    (decoded32 tieWindow) ln rn 128 (by
      change |numerical32 word - numerical32 tieWindow| ≤ _
      rw [abs_le]
      constructor <;> linarith)
  have radius : (2 : ℚ) ^ (max ((128 : Int) + 1 - Format.binary32.mantissaBits)
      Format.binary32.minExponent) / 2 = (2 : ℚ) ^ (104 : Int) := by
    have exponent : max ((128 : Int) + 1 - Format.binary32.mantissaBits)
        Format.binary32.minExponent = 105 := by decide
    rw [exponent, show (105 : Int) = 104 + 1 by norm_num,
      zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    norm_num
  have error := operation.2
  rw [radius] at error
  change |unpackedValue (UnpackedFloat.sub Format.binary32 (decoded32 word) (decoded32 tieWindow))
    - (numerical32 word - numerical32 tieWindow)| ≤ _ at error
  have rounded : Rounded (numerical32 word - numerical32 tieWindow)
      (unpackedValue (UnpackedFloat.sub Format.binary32 (decoded32 word)
        (decoded32 tieWindow))) := by
    simpa only [numerical32, model_sub_add_neg, model_neg_value, ← sub_eq_add_neg] using
      rounded_add (decoded32 word) (UnpackedFloat.neg (decoded32 tieWindow)) ln
        (model_neg_normalized _ _ rn)
  have upper := Rounded.mono rounded (binary32_rounded_exact word finite) (by linarith)
  have fits := fits_of_abs_lt _ operation.1 (by
    rw [abs_lt]
    constructor <;> linarith [(abs_le.mp error).1])
  have decoded : decoded32 (word.sub tieWindow) =
      UnpackedFloat.sub Format.binary32 (decoded32 word) (decoded32 tieWindow) := by
    change UnpackedFloat.unpack Format.binary32 (UnpackedFloat.pack Format.binary32
      (UnpackedFloat.sub Format.binary32 (Float32.Model.ofBits word.bits).unpack
        (Float32.Model.ofBits tieWindow.bits).unpack)) = _
    rw [model_ofBits32_decoded word finite, model_ofBits32_decoded tieWindow tieFinite]
    exact model_unpack_pack_normalized _ _ operation.1 fits
  have resultFinite : (word.sub tieWindow).Finite := by
    apply (model_decoded32_finite _).mp
    rw [decoded]
    exact model_normalized_finite _ _ operation.1
  refine ⟨finite_not_isNaN resultFinite, ?_⟩
  rw [← numerical32_order _ _ resultFinite finite]
  change unpackedValue (decoded32 _) ≤ _
  rw [decoded]
  exact upper

/-- No word is strictly below itself. -/
theorem less_irrefl (word : Binary32) : ¬word.Less word := fun less => lt_irrefl _ less.2.2

/-- Strict order of words is asymmetric. -/
theorem less_asymm {left right : Binary32} (less : left.Less right) : ¬right.Less left :=
  fun back => lt_asymm less.2.2 back.2.2

/-- Every member of a vector's list is one of its entries. -/
theorem vector_member {α : Type} {size : Nat} (items : Vector α size) (item : α)
    (member : item ∈ items.toList) : ∃ index : Fin size, item = items.get index := by
  obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp member
  have small : index < size := by simpa using bound
  exact ⟨⟨index, small⟩, by simp [vector_get, ← same]⟩

/-- The ordered maximum's fold ends at `top` when it starts at `top`, or below `top` with `top`
still to read, and every value it reads is `top` or below it. -/
theorem fold_top (top : Binary32) :
    ∀ (rest : List Binary32) (start : Binary32), (start = top ∨ (start.Less top ∧ top ∈ rest)) →
      (∀ value ∈ rest, value = top ∨ value.Less top) →
      rest.foldl (fun best value => if best.Less value then value else best) start = top := by
  intro rest
  induction rest with
  | nil =>
    intro start begin _
    rcases begin with same | ⟨_, absent⟩
    · exact same
    · simp at absent
  | cons value rest ih =>
    intro start begin values
    rw [List.foldl_cons]
    apply ih _ _ (fun other member => values other (List.mem_cons_of_mem _ member))
    rcases values value List.mem_cons_self with same | below
    · subst same
      refine Or.inl ?_
      rcases begin with rfl | ⟨less, _⟩
      · rw [ite_eq_right (less_irrefl _)]
      · rw [ite_eq_left less]
    · rcases begin with rfl | ⟨less, member⟩
      · exact Or.inl (ite_eq_right (less_asymm below))
      · refine Or.inr ?_
        have later : top ∈ rest := by
          rcases List.mem_cons.mp member with same | later
          · exact absurd (same ▸ below) (less_irrefl _)
          · exact later
        split
        · exact ⟨below, later⟩
        · exact ⟨less, later⟩

/-- The actions filtered by a test that admits exactly `winner` are `[winner]`. -/
theorem filter_single {size : Nat} (winner : Fin size) (keep : Fin size → Bool)
    (exact : ∀ action, keep action = true ↔ action = winner) :
    (List.finRange size).filter keep = [winner] := by
  have distinct := (List.nodup_finRange size).filter keep
  have only : ∀ action ∈ (List.finRange size).filter keep, action = winner :=
    fun action member => (exact action).mp (List.mem_filter.mp member).2
  have present : winner ∈ (List.finRange size).filter keep :=
    List.mem_filter.mpr ⟨List.mem_finRange winner, (exact winner).mpr rfl⟩
  generalize (List.finRange size).filter keep = kept at distinct only present
  match kept, distinct, only, present with
  | [], _, _, absent => simp at absent
  | action :: rest, distinct, only, _ =>
    have head := only action List.mem_cons_self
    subst head
    cases rest with
    | nil => rfl
    | cons other more =>
      have next := only other (List.mem_cons_of_mem _ List.mem_cons_self)
      subst next
      simp at distinct

/-- A finite value more than the tie window above every other is the one candidate, and the greedy
draw returns it whatever the generator. -/
theorem candidates_of_gap {count : Word.Count} (snapshot : PolicySnapshot count)
    (winner : Action count.word.toNat) (finite : (snapshot.values.get winner).Finite)
    (gap : ∀ action, action ≠ winner →
      (snapshot.values.get action).Less ((snapshot.values.get winner).sub tieWindow)) :
    snapshot.candidates = [winner] ∧ ∀ rng, (snapshot.greedy rng).1 = winner := by
  have threshold := sub_tie_le _ finite
  have topNumber := finite_not_isNaN finite
  have below : ∀ action, action ≠ winner →
      (snapshot.values.get action).Less (snapshot.values.get winner) := by
    intro action other
    obtain ⟨nan, _, lower⟩ := gap action other
    exact ⟨nan, topNumber, lt_of_lt_of_le lower threshold.2⟩
  have values : ∀ value ∈ snapshot.values.toList.drop 1,
      value = snapshot.values.get winner ∨ value.Less (snapshot.values.get winner) := by
    intro value member
    obtain ⟨action, rfl⟩ := vector_member snapshot.values value (List.mem_of_mem_drop member)
    by_cases same : action = winner
    · exact Or.inl (same ▸ rfl)
    · exact Or.inr (below action same)
  have best : snapshot.best = snapshot.values.get winner := by
    rw [PolicySnapshot.best_def]
    apply fold_top _ _ _ _ values
    by_cases first : winner = firstAction count
    · exact Or.inl (by rw [first])
    · refine Or.inr ⟨below _ (Ne.symm first), ?_⟩
      have later : winner.val ≠ 0 := fun zero => first (Fin.ext zero)
      refine List.mem_iff_getElem.mpr ⟨winner.val - 1, by simp; omega, ?_⟩
      simp only [List.getElem_drop, vector_get, Vector.getElem_toList]
      congr 1
      omega
  have candidates : snapshot.candidates = [winner] := by
    rw [PolicySnapshot.candidates_def]
    dsimp only
    rw [best]
    apply filter_single
    intro action
    rw [decide_eq_true_iff]
    constructor
    · intro tied
      by_contra other
      exact absurd tied.2.2 (not_le.mpr (gap action other).2.2)
    · rintro rfl
      exact ⟨threshold.1, topNumber, threshold.2⟩
  refine ⟨candidates, fun rng => ?_⟩
  have support := greedy_support snapshot rng
  rw [candidates] at support
  simpa using support

/-- A zero word decodes to a zero of some sign. -/
theorem zero_decoded (word : Binary32) (zero : word.isZero = true) :
    ∃ sign, decoded32 word = .zero sign := by
  rcases zero_cases word zero with rfl | rfl
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- A zero word plus a finite word has the finite word's value, for either zero sign. -/
theorem zero_add_same (zero word : Binary32) (zeroWord : zero.isZero = true)
    (finite : word.Finite) : numerical32 (zero.add word) = numerical32 word := by
  have zf := zero_finite zero zeroWord
  obtain ⟨sign, decodedZero⟩ := zero_decoded zero zeroWord
  have valid := model_unpack_format Format.binary32 (by decide) word.bits.toBitVec
    ((model_decoded32_finite word).mpr finite)
  change ModelNormalized Format.binary32 (decoded32 word) ∧
    ModelFits Format.binary32 (decoded32 word) at valid
  have normal : ModelNormalized Format.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 zero) (decoded32 word)) := by
    rw [decodedZero]
    cases sign <;> cases h : decoded32 word <;> simp_all [UnpackedFloat.add, ModelNormalized] <;>
      split_ifs <;> simp
  have fits : ModelFits Format.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 zero) (decoded32 word)) := by
    rw [decodedZero]
    cases sign <;> cases h : decoded32 word <;> simp_all [UnpackedFloat.add, ModelFits] <;>
      split_ifs <;> simp
  have decoded := model_add32_decoded zero word zf finite normal fits
  change unpackedValue (decoded32 _) = unpackedValue (decoded32 word)
  rw [decoded, decodedZero]
  cases h : decoded32 word with
  | zero other => cases sign <;> cases other <;> rfl
  | _ => cases sign <;> rfl

/-- A finite word plus a zero word keeps its value, for either zero sign. -/
theorem add_zero_same (word zero : Binary32) (finite : word.Finite)
    (zeroWord : zero.isZero = true) : numerical32 (word.add zero) = numerical32 word := by
  have zf := zero_finite zero zeroWord
  obtain ⟨sign, decodedZero⟩ := zero_decoded zero zeroWord
  have valid := model_unpack_format Format.binary32 (by decide) word.bits.toBitVec
    ((model_decoded32_finite word).mpr finite)
  change ModelNormalized Format.binary32 (decoded32 word) ∧
    ModelFits Format.binary32 (decoded32 word) at valid
  have normal : ModelNormalized Format.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 word) (decoded32 zero)) := by
    rw [decodedZero]
    cases sign <;> cases h : decoded32 word <;> simp_all [UnpackedFloat.add, ModelNormalized]
    split_ifs <;> simp
  have fits : ModelFits Format.binary32
      (UnpackedFloat.add Format.binary32 (decoded32 word) (decoded32 zero)) := by
    rw [decodedZero]
    cases sign <;> cases h : decoded32 word <;> simp_all [UnpackedFloat.add, ModelFits]
    split_ifs <;> simp
  have decoded := model_add32_decoded word zero finite zf normal fits
  change unpackedValue (decoded32 _) = unpackedValue (decoded32 word)
  rw [decoded, decodedZero]
  cases h : decoded32 word with
  | zero other => cases sign <;> cases other <;> rfl
  | _ => cases sign <;> rfl

/-- Adding one finite word to two finite words of one value gives one value: the two words are one
word, or both zero words, which add like each other. -/
theorem add_same_value (left right term : Binary32) (lf : left.Finite) (rf : right.Finite)
    (tf : term.Finite) (same : numerical32 left = numerical32 right) :
    numerical32 (left.add term) = numerical32 (right.add term) := by
  have key : left.key = right.key :=
    le_antisymm ((numerical32_order _ _ lf rf).mp same.le)
      ((numerical32_order _ _ rf lf).mp same.ge)
  rcases key_inj _ _ key with rfl | ⟨lz, rz⟩
  · rfl
  · rw [zero_add_same _ _ lz tf, zero_add_same _ _ rz tf]

/-- Where the weights outside `keep` are zero words, the ordered sum of the weights has the value
of the ordered sum of the kept weights. Every partial sum of legal weights is finite
(`CurrentPrediction.legal_weight_sum_bound`), so each step adds one word to two finite words of one
value, or a zero word to one of them. -/
theorem resting_sum {rule : ValueRule} {dimension : Dimension}
    (weight : FeatIdx dimension → Weight rule) (keep : FeatIdx dimension → Bool)
    (slots : List (FeatIdx dimension))
    (rest : ∀ slot ∈ slots, keep slot = false → (weight slot).value.isZero = true) :
    numerical32 (Binary32.sumFrom .zero (slots.map fun slot => (weight slot).value)) =
      numerical32
        (Binary32.sumFrom .zero ((slots.filter keep).map fun slot => (weight slot).value)) := by
  have finiteOf : ∀ list : List (FeatIdx dimension),
      ((list.map fun slot => (weight slot).value).foldl Binary32.add .zero).Finite := by
    intro list
    have bound := (CurrentPrediction.legal_weight_sum_bound rule (list.map weight)).1
    simpa [Binary32.sumFrom_def, List.map_map, Function.comp_def] using bound
  simp only [Binary32.sumFrom_def]
  induction slots using List.reverseRecOn with
  | nil => rfl
  | append_singleton slots slot ih =>
    have previous := ih fun other member => rest other (List.mem_append_left _ member)
    have termFinite := (CurrentPrediction.weight_numerical_bound rule (weight slot)).1
    simp only [List.filter_append, List.map_append, List.foldl_append, List.map_cons,
      List.map_nil, List.foldl_cons, List.foldl_nil, List.filter_cons, List.filter_nil]
    cases kept : keep slot with
    | true =>
      simp only [ite_true, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      exact add_same_value _ _ _ (finiteOf slots) (finiteOf (slots.filter keep)) termFinite
        previous
    | false =>
      simp only [Bool.false_eq_true, ite_false, List.map_nil, List.foldl_nil]
      exact (add_zero_same _ _ (finiteOf slots)
        (rest slot (List.mem_append_right _ List.mem_cons_self) kept)).trans previous

/-- Where a row's weights on the active slots outside `anchor` are zero words, its prediction on
the frame has the value of its prediction on `anchor`. -/
theorem resting_row {config : Acorn.Config} {dimension : Dimension}
    (learner : Managed config dimension) (features anchor : SwiftTd.ActiveSet dimension)
    (order : anchor.indices = features.indices.filter (fun slot => decide (slot ∈ anchor.indices)))
    (rest : ∀ slot, slot ∈ features.indices → slot ∉ anchor.indices →
      (learner.state.weights.get slot).value.isZero = true) :
    numerical32 (learner.state.linearPrediction features) =
      numerical32 (learner.state.linearPrediction anchor) := by
  rw [NumericState.linearPrediction_eq_sumFrom, NumericState.linearPrediction_eq_sumFrom, order]
  exact resting_sum (fun slot => learner.state.weights.get slot) _ _ fun slot member out =>
    rest slot member (by simpa using out)

/-- The ordered maximum's folds over pointwise related finite words end at related words: both
finite, with one key. -/
theorem fold_related :
    ∀ (lefts rights : List Binary32),
      List.Forall₂ (fun left right => left.Finite ∧ right.Finite ∧ left.key = right.key)
        lefts rights →
      ∀ (left right : Binary32), (left.Finite ∧ right.Finite ∧ left.key = right.key) →
        (lefts.foldl (fun best value => if best.Less value then value else best) left).Finite ∧
        (rights.foldl (fun best value => if best.Less value then value else best) right).Finite ∧
        (lefts.foldl (fun best value => if best.Less value then value else best) left).key =
          (rights.foldl (fun best value => if best.Less value then value else best) right).key := by
  intro lefts rights pair
  induction pair with
  | nil => intro left right start; exact start
  | @cons value other lefts rights related _ ih =>
    intro left right start
    simp only [List.foldl_cons]
    apply ih
    obtain ⟨lf, rf, key⟩ := start
    obtain ⟨vf, of, valueKey⟩ := related
    have decision : left.Less value ↔ right.Less other := by
      simp only [Binary32.Less, finite_not_isNaN lf, finite_not_isNaN rf, finite_not_isNaN vf,
        finite_not_isNaN of, key, valueKey, not_false_eq_true, true_and]
    by_cases less : left.Less value
    · rw [ite_eq_left less, ite_eq_left (decision.mp less)]
      exact ⟨vf, of, valueKey⟩
    · rw [ite_eq_right less, ite_eq_right (fun more => less (decision.mpr more))]
      exact ⟨lf, rf, key⟩

/-- Snapshots whose values are pointwise finite with one key have one candidate list: the two
maxima are one word or both zero words, so the two thresholds are one word. -/
theorem candidates_related {count : Word.Count} (left right : PolicySnapshot count)
    (pair : ∀ action, (left.values.get action).Finite ∧ (right.values.get action).Finite ∧
      (left.values.get action).key = (right.values.get action).key) :
    left.candidates = right.candidates := by
  have lists : List.Forall₂
      (fun left right : Binary32 => left.Finite ∧ right.Finite ∧ left.key = right.key)
      left.values.toList right.values.toList := by
    rw [List.forall₂_iff_get]
    refine ⟨by simp, fun index lb rb => ?_⟩
    have small : index < count.word.toNat := by simpa using lb
    simpa [vector_get] using pair ⟨index, small⟩
  have best := fold_related _ _ (List.forall₂_drop 1 lists) _ _ (pair (firstAction count))
  rw [← PolicySnapshot.best_def, ← PolicySnapshot.best_def] at best
  have threshold : left.best.sub tieWindow = right.best.sub tieWindow := by
    rcases key_inj _ _ best.2.2 with same | ⟨lz, rz⟩
    · rw [same]
    · exact zero_sub_tie _ _ lz rz
  rw [PolicySnapshot.candidates_def, PolicySnapshot.candidates_def]
  dsimp only
  rw [threshold]
  apply List.filter_congr
  intro action _
  obtain ⟨lf, rf, key⟩ := pair action
  simp only [Binary32.LessOrEqual, finite_not_isNaN lf, finite_not_isNaN rf, key,
    not_false_eq_true, true_and]

/-- Where every row's weights on the active slots outside `anchor` are zero words, the frame has
the near-maximum candidates of `anchor` alone. -/
theorem candidates_of_resting {count : Word.Count} {config : Acorn.Config} {dimension : Dimension}
    (controller : Controller config dimension count.word.toNat)
    (features anchor : SwiftTd.ActiveSet dimension)
    (order : anchor.indices = features.indices.filter (fun slot => decide (slot ∈ anchor.indices)))
    (rest : ∀ (row : Fin count.word.toNat) (slot : FeatIdx dimension), slot ∈ features.indices →
      slot ∉ anchor.indices →
        ((controller.learners.get row).state.weights.get slot).value.isZero = true)
    (epsilon : SwiftTd.ExploreRate) :
    (controller.snapshot features epsilon).candidates =
      (controller.snapshot anchor epsilon).candidates := by
  apply candidates_related
  intro row
  rw [Controller.snapshot_def, Controller.snapshot_def]
  dsimp only
  have lf := prediction_finite controller features row
  have rf := prediction_finite controller anchor row
  have same := resting_row (controller.learners.get row) features anchor order (rest row)
  have values : ∀ frame : SwiftTd.ActiveSet dimension, (controller.predictAll frame).get row =
      (controller.learners.get row).state.linearPrediction frame := by
    intro frame
    simp [Controller.predictAll_def, vector_get]
  rw [← values, ← values] at same
  refine ⟨lf, rf, le_antisymm ?_ ?_⟩
  · exact (numerical32_order _ _ lf rf).mp same.le
  · exact (numerical32_order _ _ rf lf).mp same.ge

end Bias

end AcornVerif.CurrentControl
