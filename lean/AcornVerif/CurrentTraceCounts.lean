import AcornVerif.CurrentFirstChoice
import AcornVerif.FloatLibBridge

namespace AcornVerif.CurrentTraceCounts
open Acorn Acorn.Features Acorn.Handcrafted
open AcornVerif.CurrentArithmetic AcornVerif.CurrentOrder AcornVerif.CurrentBackupBounds
open AcornVerif.CurrentLearner AcornVerif.CurrentPreReward AcornVerif.CurrentFeatureConsumers
open AcornVerif.CurrentControl AcornVerif.CurrentCreditHorizon AcornVerif.CurrentFirstChoice
open SwiftTd (ActiveSet)

section Words

def freshChain (criterion : Criterion) : Nat → Binary32
  | 0 => stepWord
  | age + 1 => (freshChain criterion age).mul (decayOf criterion)

theorem freshChain_facts (criterion : Criterion) (age : Nat) :
    Small (freshChain criterion age) ∧ 0 ≤ numerical32 (freshChain criterion age) ∧
      numerical32 (freshChain criterion age) ≤ numerical32 stepWord := by
  induction age with
  | zero => exact ⟨small_step, step_nonneg, le_rfl⟩
  | succ age ih =>
    have product := mul_small ih.1 (small_decay criterion)
    have lower := mul_nonneg' ih.1 (small_decay criterion) ih.2.1 (decay_nonneg criterion)
    have upper := mul_le_self ih.1 (small_decay criterion) ih.2.1 (decay_le_one criterion)
    exact ⟨small_between product.1 small_zero ih.1 (by rw [zero_value]; exact lower) upper,
      lower, le_trans upper ih.2.2⟩

theorem low_le_fresh (criterion : Criterion) (age : Nat) :
    numerical32 (lowChain criterion age) ≤ numerical32 (freshChain criterion age) := by
  induction age with
  | zero =>
    exact num_le (lowChain_facts criterion 0).1.1 small_step.1
      (by cases criterion <;> decide +kernel)
  | succ age ih =>
    exact mul_mono (lowChain_facts criterion age).1 (small_decay criterion)
      (freshChain_facts criterion age).1 (small_decay criterion)
      (lowChain_facts criterion age).2.1 (decay_nonneg criterion) ih le_rfl

theorem freshChain_above (criterion : Criterion) (age : Nat) (near : age ≤ 80) :
    numerical32 pruneWord < numerical32 (freshChain criterion age) :=
  lt_of_lt_of_le (lowChain_above criterion age near) (low_le_fresh criterion age)

theorem freshChain_antitone (criterion : Criterion) (age more : Nat) :
    numerical32 (freshChain criterion (age + more)) ≤ numerical32 (freshChain criterion age) := by
  induction more with
  | zero => exact le_rfl
  | succ more ih =>
    have facts := freshChain_facts criterion (age + more)
    exact le_trans (mul_le_self facts.1 (small_decay criterion) facts.2.1 (decay_le_one criterion))
      ih

theorem fresh_word (criterion : Criterion) (age : Nat) :
    (freshChain criterion age).Finite ∧ 0 ≤ numerical32 (freshChain criterion age) ∧
      numerical32 (freshChain criterion age) ≤ (2 : ℚ) ^ (-14 : Int) := by
  have facts := freshChain_facts criterion age
  refine ⟨facts.1.1, facts.2.1, facts.2.2.trans ?_⟩
  rw [step_value]
  norm_num

end Words

section Numbers

open AcornVerif.FloatLibBridge

theorem decay_word : decayOf .discounted = ⟨0x3f641893⟩ := by
  decide +kernel

theorem decay_value :
    numerical32 (decayOf .discounted) = 14948499 * (2 : ℚ) ^ (-24 : Int) := by
  rw [decay_word]
  change (1 : ℚ) * 14948499 * (2 : ℚ) ^ (-24 : Int) = _
  ring

theorem prune_value : numerical32 pruneWord = 9007202 * (2 : ℚ) ^ (-54 : Int) := by
  change (1 : ℚ) * 9007202 * (2 : ℚ) ^ (-54 : Int) = _
  ring

theorem fresh_step (age : Nat) (near : age ≤ 80) :
    (89099 / 100000 : ℚ) * numerical32 (freshChain .discounted age) ≤
        numerical32 (freshChain .discounted (age + 1)) ∧
      numerical32 (freshChain .discounted (age + 1)) ≤
        (89101 / 100000 : ℚ) * numerical32 (freshChain .discounted age) := by
  have facts := freshChain_facts .discounted age
  have next := freshChain_facts .discounted (age + 1)
  have above := freshChain_above .discounted age near
  have same : freshChain .discounted (age + 1) =
      (freshChain .discounted age).mul (decayOf .discounted) := rfl
  rw [same] at next ⊢
  have error := binary32_mul_relative (freshChain .discounted age) (decayOf .discounted)
    facts.1.1 (small_decay .discounted).1 next.1.1
  have e24 : (2 : ℚ) ^ (-24 : Int) = 1 / 16777216 := by norm_num
  have e54 : (2 : ℚ) ^ (-54 : Int) = 1 / 18014398509481984 := by norm_num
  rw [decay_value, e24] at error
  rw [prune_value, e54] at above
  have product : 0 ≤ numerical32 (freshChain .discounted age) * (14948499 * (1 / 16777216)) :=
    mul_nonneg facts.2.1 (by norm_num)
  rw [abs_of_nonneg product] at error
  have bounds := abs_le.mp error
  have tiny : (1 : ℚ) / 2 ^ 150 ≤ 1 / 2 ^ 100 := by norm_num
  constructor <;> linarith [bounds.1, bounds.2]

theorem fresh_ratio (age more : Nat) (near : age + more ≤ 81) :
    (89099 / 100000 : ℚ) ^ more * numerical32 (freshChain .discounted age) ≤
        numerical32 (freshChain .discounted (age + more)) ∧
      numerical32 (freshChain .discounted (age + more)) ≤
        (89101 / 100000 : ℚ) ^ more * numerical32 (freshChain .discounted age) := by
  induction more with
  | zero => simp
  | succ more ih =>
    obtain ⟨low, high⟩ := ih (by omega)
    obtain ⟨stepLow, stepHigh⟩ := fresh_step (age + more) (by omega)
    change _ ≤ numerical32 (freshChain .discounted (age + more + 1)) ∧
      numerical32 (freshChain .discounted (age + more + 1)) ≤ _
    constructor
    · calc (89099 / 100000 : ℚ) ^ (more + 1) * numerical32 (freshChain .discounted age)
          = 89099 / 100000 *
            ((89099 / 100000 : ℚ) ^ more * numerical32 (freshChain .discounted age)) := by ring
        _ ≤ 89099 / 100000 * numerical32 (freshChain .discounted (age + more)) :=
          mul_le_mul_of_nonneg_left low (by norm_num)
        _ ≤ _ := stepLow
    · calc numerical32 (freshChain .discounted (age + more + 1))
          ≤ 89101 / 100000 * numerical32 (freshChain .discounted (age + more)) := stepHigh
        _ ≤ 89101 / 100000 *
            ((89101 / 100000 : ℚ) ^ more * numerical32 (freshChain .discounted age)) :=
          mul_le_mul_of_nonneg_left high (by norm_num)
        _ = _ := by ring

theorem fresh_bounds (age : Nat) (near : age ≤ 81) :
    (89099 / 100000 : ℚ) ^ age * (13743900 * (2 : ℚ) ^ (-38 : Int)) ≤
        numerical32 (freshChain .discounted age) ∧
      numerical32 (freshChain .discounted age) ≤
        (89101 / 100000 : ℚ) ^ age * (13743900 * (2 : ℚ) ^ (-38 : Int)) := by
  have ratio := fresh_ratio 0 age (by omega)
  rw [Nat.zero_add] at ratio
  have start : numerical32 (freshChain .discounted 0) = 13743900 * (2 : ℚ) ^ (-38 : Int) :=
    step_value
  rw [start] at ratio
  exact ratio

end Numbers

section Sums

theorem repeatSum_near (word : Binary32) (finite : word.Finite)
    (nonneg : 0 ≤ numerical32 word) (small : numerical32 word ≤ (2 : ℚ) ^ (-14 : Int)) :
    ∀ count ≤ 1999, (repeatSum word count).Finite ∧
      |numerical32 (repeatSum word count) - count * numerical32 word| ≤
        count * (2 : ℚ) ^ (-28 : Int) := by
  intro count
  induction count with
  | zero =>
    intro _
    rw [repeatSum_zero]
    refine ⟨by decide, ?_⟩
    rw [zero_value]
    norm_num
  | succ count ih =>
    intro fits
    obtain ⟨sumFinite, near⟩ := ih (by omega)
    have counted : (count : ℚ) ≤ 1998 := by exact_mod_cast (by omega : count ≤ 1998)
    have product : (count : ℚ) * numerical32 word ≤ 1998 * (2 : ℚ) ^ (-14 : Int) :=
      mul_le_mul counted small nonneg (by norm_num)
    have productNonneg : 0 ≤ (count : ℚ) * numerical32 word :=
      mul_nonneg (Nat.cast_nonneg count) nonneg
    have bounds := abs_le.mp near
    have e14 : (2 : ℚ) ^ (-14 : Int) = 1 / 16384 := by norm_num
    have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
    have e3 : (2 : ℚ) ^ (-3 : Int) = 1 / 8 := by norm_num
    rw [e14] at small product
    rw [e28] at bounds near ⊢
    have step := AcornVerif.CurrentPrediction.binary32_add_finite_strict_error
      (repeatSum word count) word sumFinite finite (-3) (by norm_num) (by
        rw [e3, abs_lt]
        constructor <;> nlinarith [bounds.1, bounds.2])
    have radius : (2 : ℚ) ^ (max ((-3 : Int) - 24) (-149)) / 2 = 1 / 268435456 := by norm_num
    rw [radius] at step
    rw [repeatSum_succ]
    refine ⟨step.1, ?_⟩
    have stepBounds := abs_le.mp step.2
    rw [abs_le]
    push_cast
    constructor <;> nlinarith [bounds.1, bounds.2, stepBounds.1, stepBounds.2]

theorem repeatSum_small (word : Binary32) (finite : word.Finite)
    (nonneg : 0 ≤ numerical32 word) (small : numerical32 word ≤ (2 : ℚ) ^ (-14 : Int))
    (count : Nat) (fits : count ≤ 1999) : Small (repeatSum word count) := by
  obtain ⟨sumFinite, near⟩ := repeatSum_near word finite nonneg small count fits
  have counted : (count : ℚ) ≤ 1999 := by exact_mod_cast fits
  have product : (count : ℚ) * numerical32 word ≤ 1999 * (2 : ℚ) ^ (-14 : Int) :=
    mul_le_mul counted small nonneg (by norm_num)
  have productNonneg : 0 ≤ (count : ℚ) * numerical32 word :=
    mul_nonneg (Nat.cast_nonneg count) nonneg
  have bounds := abs_le.mp near
  have e14 : (2 : ℚ) ^ (-14 : Int) = 1 / 16384 := by norm_num
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  rw [e14] at product
  rw [e28] at bounds
  refine ⟨sumFinite, abs_le.mpr ⟨?_, ?_⟩⟩ <;> nlinarith [bounds.1, bounds.2]

theorem step_bound : numerical32 stepWord ≤ (2 : ℚ) ^ (-14 : Int) := by
  rw [step_value]
  norm_num

theorem freshSum_small (criterion : Criterion) (age count : Nat) (fits : count ≤ 1999) :
    Small (repeatSum (freshChain criterion age) count) ∧
      0 ≤ numerical32 (repeatSum (freshChain criterion age) count) ∧
      numerical32 (repeatSum (freshChain criterion age) count) ≤
        numerical32 (repeatSum stepWord count) := by
  have facts := freshChain_facts criterion age
  have total := sumFrom_le_repeat stepWord small_step
    (List.replicate count (freshChain criterion age)) .zero 0
    (fun k bound => repeatSum_small stepWord small_step.1 step_nonneg step_bound k
      (by simp only [List.length_replicate] at bound; omega))
    small_zero (le_of_eq zero_value.symm) (le_of_eq (by rw [repeatSum_zero]))
    (fun term member => by
      rw [List.eq_of_mem_replicate member]
      exact facts)
  simp only [List.length_replicate, Nat.zero_add] at total
  exact total

theorem freshSum_older (criterion : Criterion) (age count : Nat) (old : 1 ≤ age)
    (fits : count ≤ 1999) :
    numerical32 (repeatSum (freshChain criterion age) count) ≤
      numerical32 (repeatSum (freshChain criterion 1) count) := by
  have onceSmall : ∀ k ≤ 1999, Small (repeatSum (freshChain criterion 1) k) :=
    fun k bound => (freshSum_small criterion 1 k bound).1
  have facts := freshChain_facts criterion age
  have below : numerical32 (freshChain criterion age) ≤ numerical32 (freshChain criterion 1) := by
    have far := freshChain_antitone criterion 1 (age - 1)
    rwa [show 1 + (age - 1) = age by omega] at far
  have total := sumFrom_le_repeat (freshChain criterion 1) (freshChain_facts criterion 1).1
    (List.replicate count (freshChain criterion age)) .zero 0
    (fun k bound => onceSmall k (by simp only [List.length_replicate] at bound; omega))
    small_zero (le_of_eq zero_value.symm) (le_of_eq (by rw [repeatSum_zero]))
    (fun term member => by
      rw [List.eq_of_mem_replicate member]
      exact ⟨facts.1, facts.2.1, below⟩)
  simp only [List.length_replicate, Nat.zero_add] at total
  exact total.2.2

theorem repeatSum_one (word : Binary32) (finite : word.Finite) :
    numerical32 (repeatSum word 1) = numerical32 word := by
  rw [repeatSum_succ, repeatSum_zero]
  exact zero_add_same .zero word (by decide) finite

def Leads (lead : Binary32) (copies : Nat) (trail : Binary32) (fewer : Nat) : Prop :=
  (fewer : ℚ) * numerical32 trail + numerical32 tieWindow +
    ((copies : ℚ) + fewer + 1) * (2 : ℚ) ^ (-28 : Int) < (copies : ℚ) * numerical32 lead

theorem counted_lead (lead trail : Binary32) (leadFinite : lead.Finite)
    (trailFinite : trail.Finite) (leadNonneg : 0 ≤ numerical32 lead)
    (trailNonneg : 0 ≤ numerical32 trail) (leadSmall : numerical32 lead ≤ (2 : ℚ) ^ (-14 : Int))
    (trailSmall : numerical32 trail ≤ (2 : ℚ) ^ (-14 : Int)) (copies fewer : Nat)
    (fitsCopies : copies ≤ 1999) (fitsFewer : fewer ≤ 1999)
    (margin : Leads lead copies trail fewer) :
    (repeatSum trail fewer).key < ((repeatSum lead copies).sub tieWindow).key := by
  have e14 : (2 : ℚ) ^ (-14 : Int) = 1 / 16384 := by norm_num
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  have e3 : (2 : ℚ) ^ (-3 : Int) = 1 / 8 := by norm_num
  have tieRead := tie_value
  rw [e43] at tieRead
  unfold Leads at margin
  obtain ⟨sumFinite, leadNear⟩ := repeatSum_near lead leadFinite leadNonneg leadSmall copies
    fitsCopies
  obtain ⟨lessFinite, trailNear⟩ := repeatSum_near trail trailFinite trailNonneg trailSmall
    fewer fitsFewer
  rw [e28] at leadNear trailNear margin
  rw [e14] at leadSmall
  rw [tieRead] at margin
  have leadBounds := abs_le.mp leadNear
  have trailBounds := abs_le.mp trailNear
  have counted : (copies : ℚ) ≤ 1999 := by exact_mod_cast fitsCopies
  have product : (copies : ℚ) * numerical32 lead ≤ 1999 * (1 / 16384) :=
    mul_le_mul counted leadSmall leadNonneg (by norm_num)
  have productNonneg : 0 ≤ (copies : ℚ) * numerical32 lead :=
    mul_nonneg (Nat.cast_nonneg copies) leadNonneg
  have copiesNonneg : (0 : ℚ) ≤ copies := Nat.cast_nonneg copies
  obtain ⟨gapFinite, gapNear⟩ := binary32_sub_finite_strict_error (repeatSum lead copies)
    tieWindow sumFinite (by decide) (-3) (by norm_num) (by
      rw [tieRead, e3, abs_lt]
      constructor <;> linarith [leadBounds.1, leadBounds.2])
  have radius : (2 : ℚ) ^ (max ((-3 : Int) - 24) (-149)) / 2 = 1 / 268435456 := by norm_num
  rw [radius, tieRead] at gapNear
  have gapBounds := abs_le.mp gapNear
  apply (numerical32_strict_order _ _ lessFinite gapFinite).mp
  linarith [trailBounds.2, leadBounds.1, gapBounds.1]

end Sums

section Rows

variable {criterion : Criterion} {dimension : Dimension} {actions : Nat}

def Fresh (criterion : Criterion)
    (controller : Controller (criterion.config .control) dimension actions) (row : Fin actions)
    (frame : ActiveSet dimension) (age : Nat) : Prop :=
  (∀ slot ∈ frame.indices,
      slot ∈ (controller.learners.get row).state.transient.eligible ∧
        (slotOf (controller.learners.get row).state slot).z = freshChain criterion age) ∧
    ∀ slot, slot ∉ frame.indices →
      slot ∉ (controller.learners.get row).state.transient.eligible

theorem fresh_laid {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (row : Action actions) (fits : features.indices.length ≤ 1999)
    (empty : ∀ slot, slot ∉ (controller.learners.get row).state.transient.eligible) :
    Fresh criterion (controller.step features row .zero).1 row features 0 := by
  unfold Fresh
  obtain ⟨δ, delta, stepped⟩ := quiet_step_row quiet features row
  rw [stepped row]
  simp only [↓reduceIte]
  have first := quiet_first_loop (controller.learners.get row).state history row (quiet.rows row)
    (row_unique controller row) (row_supported controller row) delta quiet.vDelta
  have entry := quiet_first_entry (controller.learners.get row).state history row
    (quiet.rows row) (row_unique controller row) (row_supported controller row) delta
    quiet.vDelta
  have out : ∀ slot, slot ∉ ((controller.learners.get row).state.learnFirstLoop
      (criterion.config .control) δ controller.vDelta (decayOf criterion)).transient.eligible :=
    fun slot => (first_loop_dormant _ δ controller.vDelta (decayOf criterion) slot
      (row_unique controller row) (empty slot) ((quiet.rows row).slots slot).weight).1
  have cleared := fun slot => first.2.2 slot (out slot)
  obtain ⟨noOvershoot, -⟩ := quiet_entry _ features fits entry
  have total : (Binary32.sumFrom .zero (features.indices.map fun idx =>
      (((controller.learners.get row).state.learnFirstLoop (criterion.config .control) δ
        controller.vDelta (decayOf criterion)).transient.z.get idx).value)).isZero = true := by
    rw [Binary32.sumFrom_def]
    apply zeroWord_foldlAdd _ _ (by decide)
    intro value member
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
    have zero := (cleared slot).zero
    rw [slotOf_z] at zero
    rw [zero]
    decide
  have result := second_loop_slots (fun _ words => Cleared criterion words)
    (fun _ words => words.z = stepWord) (fun _ => True)
    (StepSizeRails.ofConfig (criterion.config .control)) _ features .zero ?_ first.1 trivial
    (fun idx _ => cleared idx)
  · refine ⟨fun slot held => ⟨?_, result.2.2.1 slot held⟩, fun slot absent => ?_⟩
    · rw [← Array.mem_toList_iff, second_loop_eligible]
      refine List.mem_append_right _ (List.mem_filter.mpr ⟨held, ?_⟩)
      have zero := (cleared slot).zero
      rw [slotOf_z] at zero
      rw [zero]
      decide
    · rw [← Array.mem_toList_iff, second_loop_eligible]
      intro member
      rcases List.mem_append.mp member with old | fresh
      · exact out slot (Array.mem_toList_iff.mp old)
      · exact absent (List.mem_filter.mp fresh).1
  · intro current vd idx _ _ pre
    simp only [noOvershoot, Bool.false_eq_true, ite_false]
    obtain ⟨words, _⟩ := quiet_second current idx _ vd pre.quiet.beta
    rw [words]
    refine ⟨?_, trivial⟩
    change (slotOf current idx).z.add (stepWord.mul (Binary32.one.sub _)) = stepWord
    rw [pre.zero, one_sub_zero total]
    decide +kernel

theorem fresh_after {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (features : ActiveSet dimension)
    (action row : Action actions) (frame : ActiveSet dimension) (age : Nat)
    (fresh : Fresh criterion controller row frame age) (other : action ≠ row)
    (above : numerical32 pruneWord < numerical32 (freshChain criterion (age + 1))) :
    Fresh criterion (controller.step features action .zero).1 row frame (age + 1) := by
  unfold Fresh
  obtain ⟨δ, delta, stepped⟩ := quiet_step_row quiet features action
  rw [stepped row]
  simp only [other, ↓reduceIte]
  have facts := freshChain_facts criterion age
  have result := first_loop_slots
    (fun _ words => SlotQuiet criterion words ∧ words.z = freshChain criterion age)
    (fun _ words => words.z = freshChain criterion (age + 1))
    (fun idx _ => idx ∉ frame.indices) δ controller.vDelta (decayOf criterion)
    (StepSizeRails.ofConfig (criterion.config .control)) ?_
    (controller.learners.get row).state (quiet.rows row).rails (row_unique controller row)
    (fun idx member => ⟨(quiet.rows row).slots idx,
      (fresh.1 idx (by_contra fun absent => fresh.2 idx absent member)).2⟩)
    (fun idx absent inside => absent (fresh.1 idx inside).1)
  · refine ⟨fun slot held => ?_, fun slot absent => ?_⟩
    · have member : slot ∈ ((controller.learners.get row).state.learnFirstLoop
          (criterion.config .control) δ controller.vDelta (decayOf criterion)).transient.eligible :=
        by_contra fun gone => result.2.2.2 slot gone held
      exact ⟨member, result.2.2.1 slot member⟩
    · exact (first_loop_dormant _ δ controller.vDelta (decayOf criterion) slot
        (row_unique controller row) (fresh.2 slot absent) ((quiet.rows row).slots slot).weight).1
  · intro current idx sameRails pre
    obtain ⟨words, same⟩ := pre
    obtain ⟨_, _, z, _, _, lastAlpha, _, _, _, _, _, prune⟩ :=
      quiet_first current idx sameRails delta quiet.vDelta words
    have lowered := mul_le_self facts.1 (small_decay criterion) facts.2.1 (decay_le_one criterion)
    have nonzero : (slotOf current idx).z.isZero = false := by
      apply Bool.eq_false_iff.mpr
      intro zero
      have zeroRead := zero_reads zero
      rw [same] at zeroRead
      have prunePositive : 0 ≤ numerical32 pruneWord := prune_nonneg
      change numerical32 pruneWord <
        numerical32 ((freshChain criterion age).mul (decayOf criterion)) at above
      linarith
    have threshold := words.reference nonzero
    have keep : (current.firstLoopElement idx δ controller.vDelta (decayOf criterion)).2 =
        false := by
      rw [prune, threshold, prune_eq, same, finite_lessOrEqual _ _
        (mul_small facts.1 (small_decay criterion)).1 (by decide)]
      simp only [decide_eq_false_iff_not, not_le]
      exact above
    refine ⟨fun pruned => absurd (keep ▸ pruned) (by decide), fun _ => ?_⟩
    rw [z, same]
    rfl

theorem fresh_total {history : List (Laid dimension actions)}
    {controller : Controller (criterion.config .control) dimension actions}
    (quiet : CtrlQuiet criterion controller history) (row : Fin actions)
    (frame : ActiveSet dimension) (age : Nat) (fresh : Fresh criterion controller row frame age)
    (features : ActiveSet dimension) (fits : features.indices.length ≤ 1999) :
    numerical32 (traceTotal controller features row) =
      numerical32 (repeatSum (freshChain criterion age)
        (features.indices.countP fun slot => decide (slot ∈ frame.indices))) := by
  unfold traceTotal
  have bounded : ∀ slots : List (FeatIdx dimension), slots.length ≤ features.indices.length →
      numerical32 (Binary32.sumFrom .zero (slots.map fun slot =>
        ((controller.learners.get row).state.transient.z.get slot).value)) =
      numerical32 (repeatSum (freshChain criterion age)
        (slots.countP fun slot => decide (slot ∈ frame.indices))) := by
    intro slots
    induction slots using List.reverseRecOn with
    | nil => intro _; rfl
    | append_singleton slots last ih =>
      intro short
      rw [List.length_append, List.length_singleton] at short
      have previous := ih (by omega)
      have leftFinite := (traces_sum_small quiet row slots (by omega)).1.1
      have counted : slots.countP (fun slot => decide (slot ∈ frame.indices)) ≤ 1999 :=
        Nat.le_trans (List.countP_le_length) (by omega)
      have rightFinite := (freshSum_small criterion age _ counted).1.1
      simp only [List.map_append, List.map_cons, List.map_nil, Binary32.sumFrom_append,
        List.countP_append, List.countP_cons, List.countP_nil]
      change numerical32 ((Binary32.sumFrom .zero (slots.map fun slot =>
        ((controller.learners.get row).state.transient.z.get slot).value)).add
          (slotOf (controller.learners.get row).state last).z) = _
      by_cases inside : last ∈ frame.indices
      · simp only [inside, decide_true, ite_true, Nat.zero_add]
        rw [repeatSum_succ, (fresh.1 last inside).2]
        exact add_same_value _ _ _ leftFinite rightFinite (freshChain_facts criterion age).1.1
          previous
      · simp only [inside, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero]
        rw [slotOf_z, registers_zero_trace _ last
          (row_supported controller row last (fresh.2 last inside))]
        exact (add_zero_same _ _ leftFinite (by decide)).trans previous
  exact bounded features.indices le_rfl

end Rows

section Lead

theorem fresh_one : freshChain .discounted 1 = ⟨0x383adb37⟩ := by
  decide +kernel

theorem fresh_one_value :
    numerical32 (freshChain .discounted 1) = 12245815 * (2 : ℚ) ^ (-38 : Int) := by
  rw [fresh_one]
  change (1 : ℚ) * 12245815 * (2 : ℚ) ^ (-38 : Int) = _
  ring

theorem share_counts (fewer copies : Nat) (share : 223 * fewer < 250 * copies)
    (positive : 1 ≤ copies) : fewer * 391898848 + 8828861 < copies * 439772032 := by
  rcases Nat.lt_or_ge fewer 19 with small | large
  · have listed : fewer = 0 ∨ fewer = 1 ∨ fewer = 2 ∨ fewer = 3 ∨ fewer = 4 ∨ fewer = 5 ∨
        fewer = 6 ∨ fewer = 7 ∨ fewer = 8 ∨ fewer = 9 ∨ fewer = 10 ∨ fewer = 11 ∨ fewer = 12 ∨
        fewer = 13 ∨ fewer = 14 ∨ fewer = 15 ∨ fewer = 16 ∨ fewer = 17 ∨ fewer = 18 := by omega
    rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · omega

theorem recent_leads (copies fewer age : Nat) (old : 1 ≤ age) (positive : 1 ≤ copies)
    (share : 223 * fewer < 250 * copies) :
    Leads stepWord copies (freshChain .discounted age) fewer := by
  have counts : (fewer : ℚ) * 391898848 + 8828861 < (copies : ℚ) * 439772032 := by
    exact_mod_cast share_counts fewer copies share positive
  have below : numerical32 (freshChain .discounted age) ≤
      numerical32 (freshChain .discounted 1) := by
    have far := freshChain_antitone .discounted 1 (age - 1)
    rwa [show 1 + (age - 1) = age by omega] at far
  have scaled := mul_le_mul_of_nonneg_left below (Nat.cast_nonneg (α := ℚ) fewer)
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  have e38 : (2 : ℚ) ^ (-38 : Int) = 1 / 274877906944 := by norm_num
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  rw [fresh_one_value, e38] at scaled
  unfold Leads
  rw [step_value, tie_value, e28, e38, e43]
  linarith

theorem fresh_lead (fewer copies : Nat) (order : fewer ≤ copies) (positive : 1 ≤ copies)
    (fits : copies ≤ 1999) :
    (repeatSum (freshChain .discounted 1) fewer).key <
      ((repeatSum stepWord copies).sub tieWindow).key :=
  counted_lead stepWord (freshChain .discounted 1) small_step.1 (fresh_word .discounted 1).1
    step_nonneg (fresh_word .discounted 1).2.1 step_bound (fresh_word .discounted 1).2.2 copies
    fewer fits (by omega) (recent_leads copies fewer 1 le_rfl positive (by omega))

theorem fresh_fourteen (age : Nat) (recent : age ≤ 14) :
    (99 : ℚ) / 10000000 ≤ numerical32 (freshChain .discounted age) := by
  have low := (fresh_bounds 14 (by omega)).1
  have far := freshChain_antitone .discounted age (14 - age)
  rw [show age + (14 - age) = 14 by omega] at far
  have number : (99 : ℚ) / 10000000 ≤
      (89099 / 100000 : ℚ) ^ 14 * (13743900 * (2 : ℚ) ^ (-38 : Int)) := by norm_num
  linarith

theorem own_alone (age copies : Nat) (recent : age ≤ 14) (positive : 1 ≤ copies) :
    Leads (freshChain .discounted age) copies .zero 0 := by
  have word := fresh_fourteen age recent
  have atLeast : (1 : ℚ) ≤ copies := by exact_mod_cast positive
  have big := mul_le_mul_of_nonneg_left word (by linarith : (0 : ℚ) ≤ copies)
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  unfold Leads
  rw [tie_value, e28, e43]
  simp only [Nat.cast_zero, zero_mul, zero_add, add_zero]
  linarith

theorem earlier_leads (age more copies fewer : Nat) (recent : age ≤ 14) (older : 1 ≤ more)
    (positive : 1 ≤ copies) (order : fewer ≤ copies) :
    Leads (freshChain .discounted age) copies (freshChain .discounted (age + more)) fewer := by
  have word := fresh_fourteen age recent
  have step := (fresh_ratio age 1 (by omega)).2
  rw [pow_one] at step
  have far := freshChain_antitone .discounted (age + 1) (more - 1)
  rw [show age + 1 + (more - 1) = age + more by omega] at far
  have trailNonneg := (fresh_word .discounted (age + more)).2.1
  have atLeast : (1 : ℚ) ≤ copies := by exact_mod_cast positive
  have ordered : (fewer : ℚ) ≤ copies := by exact_mod_cast order
  have copiesNonneg : (0 : ℚ) ≤ copies := by linarith
  have first := mul_le_mul_of_nonneg_right ordered trailNonneg
  have second := mul_le_mul_of_nonneg_left (far.trans step) copiesNonneg
  have big := mul_le_mul_of_nonneg_left word copiesNonneg
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  unfold Leads
  rw [tie_value, e28, e43]
  linarith

theorem later_leads (age more copies fewer : Nat) (recent : age ≤ 14) (newer : 1 ≤ more)
    (within : more ≤ age) (positive : 1 ≤ copies)
    (share : fewer * 100 ^ more ≤ 89 ^ more * (copies - 1)) :
    Leads (freshChain .discounted age) copies (freshChain .discounted (age - more)) fewer := by
  have word := fresh_fourteen age recent
  have ratio := (fresh_ratio (age - more) more (by omega)).1
  rw [show age - more + more = age by omega] at ratio
  have trailNonneg := (fresh_word .discounted (age - more)).2.1
  have atLeast : (1 : ℚ) ≤ copies := by exact_mod_cast positive
  have restNonneg : (0 : ℚ) ≤ (copies : ℚ) - 1 := by linarith
  have cast : ((fewer * 100 ^ more : ℕ) : ℚ) ≤ ((89 ^ more * (copies - 1) : ℕ) : ℚ) :=
    Nat.cast_le.mpr share
  push_cast [Nat.cast_sub positive] at cast
  have shareLe : (fewer : ℚ) ≤ (89 / 100 : ℚ) ^ more * ((copies : ℚ) - 1) := by
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact cast
  have powLe : (89 / 100 : ℚ) ^ more ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have fewerLe : (fewer : ℚ) ≤ (copies : ℚ) - 1 :=
    shareLe.trans (mul_le_of_le_one_left restNonneg powLe)
  have split : (89 / 100 : ℚ) ^ more = (89000 / 89099 : ℚ) ^ more * (89099 / 100000) ^ more := by
    rw [← mul_pow]
    norm_num
  have shrink : (89000 / 89099 : ℚ) ^ more ≤ 89000 / 89099 :=
    pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have key : (89 / 100 : ℚ) ^ more * numerical32 (freshChain .discounted (age - more)) ≤
      89000 / 89099 * numerical32 (freshChain .discounted age) := by
    rw [split, mul_assoc]
    exact mul_le_mul shrink ratio (mul_nonneg (by positivity) trailNonneg) (by norm_num)
  have first := mul_le_mul_of_nonneg_right shareLe trailNonneg
  have second := mul_le_mul_of_nonneg_left key restNonneg
  have big := mul_le_mul_of_nonneg_left word restNonneg
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  unfold Leads
  rw [tie_value, e28, e43]
  nlinarith [first, second, big, word, fewerLe]

theorem slack_needed :
    9 * numerical32 (freshChain .discounted 1) - 8 * numerical32 stepWord <
      numerical32 tieWindow := by
  rw [fresh_one_value, step_value, tie_value]
  norm_num

end Lead

section Candidate

variable {count : Word.Count}

theorem margin_candidate (snapshot : PolicySnapshot count) (winner : Action count.word.toNat)
    (lead : Binary32) (copies : Nat) (leadFinite : lead.Finite)
    (leadNonneg : 0 ≤ numerical32 lead) (leadSmall : numerical32 lead ≤ (2 : ℚ) ^ (-14 : Int))
    (fits : copies ≤ 1999) (finite : ∀ action, (snapshot.values.get action).Finite)
    (leads : numerical32 (snapshot.values.get winner) = numerical32 (repeatSum lead copies))
    (trails : ∀ action, action ≠ winner → ∃ (trail : Binary32) (fewer : Nat),
      trail.Finite ∧ 0 ≤ numerical32 trail ∧ numerical32 trail ≤ (2 : ℚ) ^ (-14 : Int) ∧
        fewer ≤ 1999 ∧
        numerical32 (snapshot.values.get action) ≤ numerical32 (repeatSum trail fewer) ∧
        Leads lead copies trail fewer) :
    snapshot.candidates = [winner] ∧ ∀ rng, (snapshot.greedy rng).1 = winner := by
  have sumFinite : (repeatSum lead copies).Finite :=
    (repeatSum_near lead leadFinite leadNonneg leadSmall copies fits).1
  have key : (snapshot.values.get winner).key = (repeatSum lead copies).key :=
    le_antisymm ((numerical32_order _ _ (finite winner) sumFinite).mp leads.le)
      ((numerical32_order _ _ sumFinite (finite winner)).mp leads.ge)
  have threshold : (snapshot.values.get winner).sub tieWindow =
      (repeatSum lead copies).sub tieWindow := by
    rcases key_inj _ _ key with equal | ⟨leftZero, rightZero⟩
    · rw [equal]
    · exact zero_sub_tie _ _ leftZero rightZero
  apply candidates_of_gap snapshot winner (finite winner)
  intro action other
  obtain ⟨trail, fewer, trailFinite, trailNonneg, trailSmall, fitsFewer, below, margin⟩ :=
    trails action other
  have lessFinite := (repeatSum_near trail trailFinite trailNonneg trailSmall fewer fitsFewer).1
  have belowKey := (numerical32_order _ _ (finite action) lessFinite).mp below
  have gap := counted_lead lead trail leadFinite trailFinite leadNonneg trailNonneg leadSmall
    trailSmall copies fewer fits fitsFewer margin
  rw [threshold]
  exact ⟨finite_not_isNaN (finite action), (sub_tie_le _ sumFinite).1,
    lt_of_le_of_lt belowKey gap⟩

theorem counted_candidate (snapshot : PolicySnapshot count) (winner : Action count.word.toNat)
    (copies : Nat) (positive : 1 ≤ copies) (fits : copies ≤ 1999)
    (finite : ∀ action, (snapshot.values.get action).Finite)
    (leads : numerical32 (snapshot.values.get winner) = numerical32 (repeatSum stepWord copies))
    (trails : ∀ action, action ≠ winner → ∃ fewer, fewer ≤ copies ∧
      numerical32 (snapshot.values.get action) ≤
        numerical32 (repeatSum (freshChain .discounted 1) fewer)) :
    snapshot.candidates = [winner] ∧ ∀ rng, (snapshot.greedy rng).1 = winner := by
  have once := fresh_word .discounted 1
  refine margin_candidate snapshot winner stepWord copies small_step.1 step_nonneg step_bound
    fits finite leads fun action other => ?_
  obtain ⟨fewer, order, below⟩ := trails action other
  exact ⟨freshChain .discounted 1, fewer, once.1, once.2.1, once.2.2, by omega, below,
    recent_leads copies fewer 1 le_rfl positive (by omega)⟩

theorem stale_candidate (snapshot : PolicySnapshot count) (earlier : Action count.word.toNat)
    (age : Nat) (old : 15 ≤ age) (near : age ≤ 80)
    (finite : ∀ action, (snapshot.values.get action).Finite)
    (top : ∀ action, numerical32 (snapshot.values.get action) ≤
      numerical32 (repeatSum (freshChain .discounted age) 1))
    (second : numerical32 (snapshot.values.get earlier) =
      numerical32 (repeatSum (freshChain .discounted (age + 1)) 1)) :
    earlier ∈ snapshot.candidates := by
  obtain ⟨⟨best, bestIs⟩, keys⟩ := best_bounds snapshot finite
  have bestFinite : snapshot.best.Finite := bestIs ▸ finite best
  have upper : numerical32 snapshot.best ≤ numerical32 (freshChain .discounted age) := by
    rw [bestIs, ← repeatSum_one _ (fresh_word .discounted age).1]
    exact top best
  have lower : numerical32 (snapshot.values.get earlier) ≤ numerical32 snapshot.best :=
    (numerical32_order _ _ (finite earlier) bestFinite).mpr (keys earlier)
  rw [repeatSum_one _ (fresh_word .discounted (age + 1)).1] at second
  have step := (fresh_step age near).1
  have far := freshChain_antitone .discounted 15 (age - 15)
  rw [show 15 + (age - 15) = age by omega] at far
  have high := (fresh_bounds 15 (by omega)).2
  have number : (89101 / 100000 : ℚ) ^ 15 * (13743900 * (2 : ℚ) ^ (-38 : Int)) ≤
      886 / 100000000 := by norm_num
  have nonneg := (fresh_word .discounted (age + 1)).2.1
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  have e3 : (2 : ℚ) ^ (-3 : Int) = 1 / 8 := by norm_num
  have tieRead := tie_value
  rw [e43] at tieRead
  obtain ⟨gapFinite, gapNear⟩ := binary32_sub_finite_strict_error snapshot.best tieWindow
    bestFinite (by decide) (-3) (by norm_num) (by
      rw [tieRead, e3, abs_lt]
      constructor <;> linarith)
  have radius : (2 : ℚ) ^ (max ((-3 : Int) - 24) (-149)) / 2 = 1 / 268435456 := by norm_num
  rw [radius, tieRead] at gapNear
  have gapBounds := abs_le.mp gapNear
  rw [PolicySnapshot.candidates_def]
  dsimp only
  refine List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true ⟨finite_not_isNaN gapFinite,
    finite_not_isNaN (finite earlier), ?_⟩⟩
  exact (numerical32_order _ _ gapFinite (finite earlier)).mp (by linarith [gapBounds.2])

end Candidate

section Shared

variable {dimension : Dimension}

def shared (frame laid : ActiveSet dimension) : Nat :=
  frame.indices.countP fun slot => decide (slot ∈ laid.indices)

theorem shared_le (frame laid : ActiveSet dimension) :
    shared frame laid ≤ frame.indices.length :=
  List.countP_le_length

theorem shared_self (frame : ActiveSet dimension) :
    shared frame frame = frame.indices.length :=
  List.countP_eq_length.mpr fun _ member => decide_eq_true member

end Shared

section Run

open AcornVerif.CurrentFirstCredit AcornVerif.CurrentExplorer AcornVerif.CurrentGridWorld

variable {interface : Interface} {profile : FeatureProfile} {config : Features.Config}
  {dimension : Dimension} {planning : PlanningSelection}

theorem loop_fresh (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (laid : Nat) :
    ∀ gap : Nat, gap ≤ 80 →
      agent.clock.toNat + (laid + 1 + gap) ≤ config.tester.maturity →
      (∀ earlier, earlier < laid + 1 + gap →
        (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero) →
      (∀ earlier, earlier < laid + 1 + gap →
        (laidAt agent world start earlier).features.indices.length ≤ 1999) →
      (∀ other, other < laid + 1 + gap → other ≠ laid →
        laid ≤ other + creditReach .discounted →
        Kernel.actionAt world (executedAgent agent) start other ≠
          Kernel.actionAt world (executedAgent agent) start laid) →
      Fresh .discounted
        (controlOf (Kernel.memoryAt world (executedAgent agent) start (laid + 1 + gap)))
        (laidAt agent world start laid).row (laidAt agent world start laid).features gap := by
  intro gap
  induction gap with
  | zero =>
    intro _ young silent fits once
    obtain ⟨ctrlLaid, equation⟩ := loop_silent primitive perStep agent [] quiet ctrl world
      start laid young silent fits
    rw [List.nil_append] at ctrlLaid
    change Fresh .discounted
      (controlOf (Kernel.memoryAt world (executedAgent agent) start (laid + 1))) _ _ 0
    rw [equation]
    refine fresh_laid ctrlLaid _ _ (fits laid (by omega)) fun slot => ?_
    exact (ctrlQuiet_dormant ctrlLaid _ slot (unlaid_window agent world start laid _ _ slot
      fun earlier early within same => absurd (same.trans (laidAt_row agent world start laid))
        (once earlier (by omega) (by omega) within))).1
  | succ gap ih =>
    intro near young silent fits once
    have before := ih (by omega) (by omega) (fun earlier early => silent earlier (by omega))
      (fun earlier early => fits earlier (by omega))
      (fun other early apart within => once other (by omega) apart within)
    obtain ⟨ctrlHere, equation⟩ := loop_silent primitive perStep agent [] quiet ctrl world
      start (laid + 1 + gap) young silent fits
    rw [List.nil_append] at ctrlHere
    change Fresh .discounted
      (controlOf (Kernel.memoryAt world (executedAgent agent) start (laid + 1 + gap + 1))) _ _
      (gap + 1)
    rw [equation]
    refine fresh_after ctrlHere _ _ _ _ gap before ?_
      (freshChain_above .discounted (gap + 1) near)
    rw [laidAt_row, laidAt_row]
    exact once (laid + 1 + gap) (by omega) (by omega) (by omega)

theorem loop_totals (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999) :
    (∀ earlier age, earlier + age = last →
      numerical32 (traceTotal
          (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1))) frame
          (Kernel.actionAt world (executedAgent agent) start earlier)) =
        numerical32 (repeatSum (freshChain .discounted age) (frame.indices.countP fun slot =>
          decide (slot ∈ (laidAt agent world start earlier).features.indices)))) ∧
      ∀ action, (∀ earlier, earlier < last + 1 →
          Kernel.actionAt world (executedAgent agent) start earlier ≠ action) →
        (traceTotal (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1)))
          frame action).isZero = true := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent [] quiet ctrl world start
    (last + 1) young silent fits
  rw [List.nil_append] at ctrlPaid
  refine ⟨fun earlier age sum => ?_, fun action untaken => ?_⟩
  · subst sum
    have fresh := loop_fresh primitive perStep agent quiet ctrl world start earlier age
      (by omega) (by omega) (fun other early => silent other (by omega))
      (fun other early => fits other (by omega))
      (fun other early apart _ => distinct other earlier (by omega) (by omega) apart)
    rw [laidAt_row, show earlier + 1 + age = earlier + age + 1 by omega] at fresh
    exact fresh_total ctrlPaid _ _ age fresh frame fitsFrame
  · exact unlaid_total ctrlPaid frame action fun held _ =>
      unlaid_window agent world start (last + 1) _ action held
        fun earlier early _ same => absurd same (untaken earlier early)

theorem paid_candidates (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (paid : Nat)
    (young : agent.clock.toNat + paid < config.tester.maturity)
    (silent : ∀ earlier, earlier < paid →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent agent) start paid).reward = .one)
    (fits : ∀ earlier, earlier < paid →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (epsilon : SwiftTd.ExploreRate) :
    ((controlOf (Kernel.memoryAt world (executedAgent agent) start (paid + 1))).snapshot frame
        epsilon).candidates =
      (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start paid)) frame
        epsilon).candidates := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent [] quiet ctrl world start paid
    (by omega) silent fits
  rw [List.nil_append] at ctrlPaid
  rw [loop_paid primitive perStep agent world start paid young pays]
  exact reward_candidates ctrlPaid _ _ frame fitsFrame epsilon

theorem leading_candidate (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (taken : Nat) (early : taken ≤ last)
    (alone : Leads (freshChain .discounted (last - taken))
      (shared frame (laidAt agent world start taken).features) .zero 0)
    (margin : ∀ other, other ≤ last → other ≠ taken →
      Leads (freshChain .discounted (last - taken))
        (shared frame (laidAt agent world start taken).features)
        (freshChain .discounted (last - other))
        (shared frame (laidAt agent world start other).features))
    (epsilon : SwiftTd.ExploreRate) :
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1))) frame
        epsilon).candidates = [Kernel.actionAt world (executedAgent agent) start taken] ∧
      ∀ rng, ((tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start
        (last + 1))) frame epsilon).greedy rng).1 =
          Kernel.actionAt world (executedAgent agent) start taken := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent [] quiet ctrl world start
    (last + 1) young silent fits
  rw [List.nil_append] at ctrlPaid
  obtain ⟨totals, untaken⟩ := loop_totals primitive perStep agent quiet ctrl world start last
    near young silent fits distinct frame fitsFrame
  have word := fresh_word .discounted
  have counted : ∀ laid : ActiveSet dimension, shared frame laid ≤ 1999 :=
    fun laid => Nat.le_trans (shared_le frame laid) fitsFrame
  refine margin_candidate _ _ (freshChain .discounted (last - taken))
    (shared frame (laidAt agent world start taken).features) (word _).1 (word _).2.1
    (word _).2.2 (counted _) (fun action => ?_) ?_ fun action other => ?_
  · rw [tracePolicy_value]
    exact (traces_sum_small ctrlPaid action frame.indices fitsFrame).1.1
  · rw [tracePolicy_value]
    exact totals taken (last - taken) (by omega)
  · rw [tracePolicy_value]
    by_cases once : ∃ earlier, earlier < last + 1 ∧
        Kernel.actionAt world (executedAgent agent) start earlier = action
    · obtain ⟨earlier, before, rfl⟩ := once
      have apart : earlier ≠ taken := fun same => other (by rw [same])
      exact ⟨freshChain .discounted (last - earlier),
        shared frame (laidAt agent world start earlier).features, (word _).1, (word _).2.1,
        (word _).2.2, counted _, le_of_eq (totals earlier (last - earlier) (by omega)),
        margin earlier (by omega) apart⟩
    · refine ⟨.zero, 0, by decide, le_of_eq zero_value.symm, ?_, Nat.zero_le _, ?_, alone⟩
      · rw [zero_value]
        positivity
      · rw [zero_reads (untaken action fun earlier before same => once ⟨earlier, before, same⟩),
          repeatSum_zero, zero_value]

theorem first_choice_leading (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (declared : profile.rate = .declared)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) < config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent agent) start (last + 1)).reward = .one)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (fitsNext : (laidAt agent world start (last + 2)).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (taken : Nat) (early : taken ≤ last)
    (alone : Leads (freshChain .discounted (last - taken))
      (shared (laidAt agent world start (last + 2)).features
        (laidAt agent world start taken).features) .zero 0)
    (margin : ∀ other, other ≤ last → other ≠ taken →
      Leads (freshChain .discounted (last - taken))
        (shared (laidAt agent world start (last + 2)).features
          (laidAt agent world start taken).features)
        (freshChain .discounted (last - other))
        (shared (laidAt agent world start (last + 2)).features
          (laidAt agent world start other).features))
    (unserved : ((explorerOf agent.control).after (last + 2)).run.bind ExploratoryRun.serve =
      none)
    (calm : (beginExploration interface.actions declaredRate
      ((explorerOf agent.control).after (last + 2)).rng).1 = none) :
    Kernel.actionAt world (executedAgent agent) start (last + 2) =
      Kernel.actionAt world (executedAgent agent) start taken := by
  have chosen := first_choice primitive perStep declared agent [] quiet ctrl world start
    (last + 1) young silent pays fits fitsNext
  have greedy := Explorer.stepOver_greedy ((explorerOf agent.control).after (last + 2))
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1)))
      (laidAt agent world start (last + 2)).features declaredRate) unserved calm
  have candidate := (leading_candidate primitive perStep agent quiet ctrl world start last near
    (by omega) silent fits distinct (laidAt agent world start (last + 2)).features fitsNext
    taken early alone margin declaredRate).2
  rw [chosen, greedy]
  exact candidate _

theorem recent_candidate (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (shares : 1 ≤ shared frame (laidAt agent world start last).features)
    (most : ∀ earlier, earlier < last →
      223 * shared frame (laidAt agent world start earlier).features <
        250 * shared frame (laidAt agent world start last).features)
    (epsilon : SwiftTd.ExploreRate) :
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1))) frame
        epsilon).candidates = [Kernel.actionAt world (executedAgent agent) start last] ∧
      ∀ rng, ((tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start
        (last + 1))) frame epsilon).greedy rng).1 =
          Kernel.actionAt world (executedAgent agent) start last := by
  refine leading_candidate primitive perStep agent quiet ctrl world start last near young silent
    fits distinct frame fitsFrame last le_rfl ?_ (fun other before apart => ?_) epsilon
  · rw [Nat.sub_self]
    exact own_alone 0 _ (by omega) shares
  · rw [Nat.sub_self]
    exact recent_leads _ _ (last - other) (by omega) shares (most other (by omega))

theorem overlap_candidate (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (most : 223 * frame.indices.length <
      250 * shared frame (laidAt agent world start last).features)
    (epsilon : SwiftTd.ExploreRate) :
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1))) frame
        epsilon).candidates = [Kernel.actionAt world (executedAgent agent) start last] ∧
      ∀ rng, ((tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start
        (last + 1))) frame epsilon).greedy rng).1 =
          Kernel.actionAt world (executedAgent agent) start last :=
  recent_candidate primitive perStep agent quiet ctrl world start last near young silent fits
    distinct frame fitsFrame (by omega)
    (fun earlier _ => by
      have fewer := shared_le frame (laidAt agent world start earlier).features
      omega)
    epsilon

theorem last_candidate (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (frame : ActiveSet dimension) (fitsFrame : frame.indices.length ≤ 1999)
    (shares : 1 ≤ frame.indices.countP fun slot =>
      decide (slot ∈ (laidAt agent world start last).features.indices))
    (most : ∀ earlier, earlier < last →
      (frame.indices.countP fun slot =>
        decide (slot ∈ (laidAt agent world start earlier).features.indices)) ≤
      frame.indices.countP fun slot =>
        decide (slot ∈ (laidAt agent world start last).features.indices))
    (epsilon : SwiftTd.ExploreRate) :
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1))) frame
        epsilon).candidates = [Kernel.actionAt world (executedAgent agent) start last] ∧
      ∀ rng, ((tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start
        (last + 1))) frame epsilon).greedy rng).1 =
          Kernel.actionAt world (executedAgent agent) start last :=
  recent_candidate primitive perStep agent quiet ctrl world start last near young silent fits
    distinct frame fitsFrame shares
    (fun earlier before => by
      have fewer := most earlier before
      unfold shared
      omega)
    epsilon

theorem first_choice_recent (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (declared : profile.rate = .declared)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) < config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent agent) start (last + 1)).reward = .one)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (fitsNext : (laidAt agent world start (last + 2)).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (shares : 1 ≤ shared (laidAt agent world start (last + 2)).features
      (laidAt agent world start last).features)
    (most : ∀ earlier, earlier < last →
      223 * shared (laidAt agent world start (last + 2)).features
          (laidAt agent world start earlier).features <
        250 * shared (laidAt agent world start (last + 2)).features
          (laidAt agent world start last).features)
    (unserved : ((explorerOf agent.control).after (last + 2)).run.bind ExploratoryRun.serve =
      none)
    (calm : (beginExploration interface.actions declaredRate
      ((explorerOf agent.control).after (last + 2)).rng).1 = none) :
    Kernel.actionAt world (executedAgent agent) start (last + 2) =
      Kernel.actionAt world (executedAgent agent) start last := by
  have chosen := first_choice primitive perStep declared agent [] quiet ctrl world start
    (last + 1) young silent pays fits fitsNext
  have greedy := Explorer.stepOver_greedy ((explorerOf agent.control).after (last + 2))
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1)))
      (laidAt agent world start (last + 2)).features declaredRate) unserved calm
  have candidate := (recent_candidate primitive perStep agent quiet ctrl world start last near
    (by omega) silent fits distinct (laidAt agent world start (last + 2)).features fitsNext
    shares most declaredRate).2
  rw [chosen, greedy]
  exact candidate _

theorem first_choice_last (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep) (declared : profile.rate = .declared)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) < config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (pays : (Kernel.perceptAt world (executedAgent agent) start (last + 1)).reward = .one)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (fitsNext : (laidAt agent world start (last + 2)).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (shares : 1 ≤ (laidAt agent world start (last + 2)).features.indices.countP fun slot =>
      decide (slot ∈ (laidAt agent world start last).features.indices))
    (most : ∀ earlier, earlier < last →
      ((laidAt agent world start (last + 2)).features.indices.countP fun slot =>
        decide (slot ∈ (laidAt agent world start earlier).features.indices)) ≤
      (laidAt agent world start (last + 2)).features.indices.countP fun slot =>
        decide (slot ∈ (laidAt agent world start last).features.indices))
    (unserved : ((explorerOf agent.control).after (last + 2)).run.bind ExploratoryRun.serve =
      none)
    (calm : (beginExploration interface.actions declaredRate
      ((explorerOf agent.control).after (last + 2)).rng).1 = none) :
    Kernel.actionAt world (executedAgent agent) start (last + 2) =
      Kernel.actionAt world (executedAgent agent) start last :=
  first_choice_recent primitive perStep declared agent quiet ctrl world start last near young
    silent pays fits fitsNext distinct shares
    (fun earlier before => by
      have fewer := most earlier before
      unfold shared
      omega)
    unserved calm

theorem own_candidate (primitive : profile.usesHierarchy = false)
    (perStep : profile.credit = .perStep)
    (agent : Agent interface profile config .discounted dimension planning)
    (quiet : Quiet agent.control) (ctrl : CtrlQuiet .discounted (controlOf agent) [])
    (world : Kernel.World interface) (start : world.State) (last : Nat) (near : last ≤ 80)
    (young : agent.clock.toNat + (last + 1) ≤ config.tester.maturity)
    (silent : ∀ earlier, earlier < last + 1 →
      (Kernel.perceptAt world (executedAgent agent) start earlier).reward = .zero)
    (fits : ∀ earlier, earlier < last + 1 →
      (laidAt agent world start earlier).features.indices.length ≤ 1999)
    (distinct : ∀ one two, one < last + 1 → two < last + 1 → one ≠ two →
      Kernel.actionAt world (executedAgent agent) start one ≠
        Kernel.actionAt world (executedAgent agent) start two)
    (taken : Nat) (early : taken ≤ last) (recent : last ≤ taken + 14)
    (holds : 1 ≤ (laidAt agent world start taken).features.indices.length)
    (later : ∀ more, 1 ≤ more → taken + more ≤ last →
      shared (laidAt agent world start taken).features
          (laidAt agent world start (taken + more)).features * 100 ^ more ≤
        89 ^ more * ((laidAt agent world start taken).features.indices.length - 1))
    (epsilon : SwiftTd.ExploreRate) :
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1)))
        (laidAt agent world start taken).features epsilon).candidates =
          [Kernel.actionAt world (executedAgent agent) start taken] ∧
      ∀ rng, ((tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start
        (last + 1))) (laidAt agent world start taken).features epsilon).greedy rng).1 =
          Kernel.actionAt world (executedAgent agent) start taken := by
  refine leading_candidate primitive perStep agent quiet ctrl world start last near young silent
    fits distinct _ (fits taken (by omega)) taken early ?_ (fun other before apart => ?_) epsilon
  · rw [shared_self]
    exact own_alone _ _ (by omega) holds
  · rw [shared_self]
    rcases Nat.lt_or_gt_of_ne apart with below | above
    · have lead := earlier_leads (last - taken) (taken - other)
        (laidAt agent world start taken).features.indices.length
        (shared (laidAt agent world start taken).features (laidAt agent world start other).features)
        (by omega) (by omega) holds (shared_le _ _)
      rwa [show last - taken + (taken - other) = last - other by omega] at lead
    · have share := later (other - taken) (by omega) (by omega)
      rw [show taken + (other - taken) = other by omega] at share
      have lead := later_leads (last - taken) (other - taken) _ _ (by omega) (by omega)
        (by omega) holds share
      rwa [show last - taken - (other - taken) = last - other by omega] at lead

end Run

end AcornVerif.CurrentTraceCounts
