import AcornVerif.CurrentFirstChoice

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

end Words

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

theorem fresh_lead (fewer copies : Nat) (order : fewer ≤ copies) (positive : 1 ≤ copies)
    (fits : copies ≤ 1999) :
    (repeatSum (freshChain .discounted 1) fewer).key <
      ((repeatSum stepWord copies).sub tieWindow).key := by
  have e14 : (2 : ℚ) ^ (-14 : Int) = 1 / 16384 := by norm_num
  have e28 : (2 : ℚ) ^ (-28 : Int) = 1 / 268435456 := by norm_num
  have e38 : (2 : ℚ) ^ (-38 : Int) = 1 / 274877906944 := by norm_num
  have e43 : (2 : ℚ) ^ (-43 : Int) = 1 / 8796093022208 := by norm_num
  have e3 : (2 : ℚ) ^ (-3 : Int) = 1 / 8 := by norm_num
  have stepRead := step_value
  have onceRead := fresh_one_value
  have tieRead := tie_value
  rw [e38] at stepRead onceRead
  rw [e43] at tieRead
  obtain ⟨leadFinite, leadNear⟩ := repeatSum_near stepWord small_step.1 step_nonneg step_bound
    copies fits
  obtain ⟨trailFinite, trailNear⟩ := repeatSum_near (freshChain .discounted 1)
    (freshChain_facts .discounted 1).1.1 (freshChain_facts .discounted 1).2.1
    (by rw [onceRead, e14]; norm_num) fewer (by omega)
  rw [stepRead, e28] at leadNear
  rw [onceRead, e28] at trailNear
  have leadBounds := abs_le.mp leadNear
  have trailBounds := abs_le.mp trailNear
  have counted : (copies : ℚ) ≤ 1999 := by exact_mod_cast fits
  have atLeast : (1 : ℚ) ≤ copies := by exact_mod_cast positive
  have ordered : (fewer : ℚ) ≤ copies := by exact_mod_cast order
  have fewerNonneg : (0 : ℚ) ≤ fewer := Nat.cast_nonneg fewer
  obtain ⟨gapFinite, gapNear⟩ := binary32_sub_finite_strict_error (repeatSum stepWord copies)
    tieWindow leadFinite (by decide) (-3) (by norm_num) (by
      rw [tieRead, e3, abs_lt]
      constructor <;> linarith [leadBounds.1, leadBounds.2])
  have radius : (2 : ℚ) ^ (max ((-3 : Int) - 24) (-149)) / 2 = 1 / 268435456 := by norm_num
  rw [radius, tieRead] at gapNear
  have gapBounds := abs_le.mp gapNear
  apply (numerical32_strict_order _ _ trailFinite gapFinite).mp
  linarith [trailBounds.2, leadBounds.1, gapBounds.1]

end Lead

section Candidate

variable {count : Word.Count}

theorem counted_candidate (snapshot : PolicySnapshot count) (winner : Action count.word.toNat)
    (copies : Nat) (positive : 1 ≤ copies) (fits : copies ≤ 1999)
    (finite : ∀ action, (snapshot.values.get action).Finite)
    (leads : numerical32 (snapshot.values.get winner) = numerical32 (repeatSum stepWord copies))
    (trails : ∀ action, action ≠ winner → ∃ fewer, fewer ≤ copies ∧
      numerical32 (snapshot.values.get action) ≤
        numerical32 (repeatSum (freshChain .discounted 1) fewer)) :
    snapshot.candidates = [winner] ∧ ∀ rng, (snapshot.greedy rng).1 = winner := by
  have sumFinite : (repeatSum stepWord copies).Finite :=
    (freshSum_small .discounted 0 copies fits).1.1
  have key : (snapshot.values.get winner).key = (repeatSum stepWord copies).key :=
    le_antisymm ((numerical32_order _ _ (finite winner) sumFinite).mp leads.le)
      ((numerical32_order _ _ sumFinite (finite winner)).mp leads.ge)
  have lead := fresh_lead 0 copies (Nat.zero_le _) positive fits
  have threshold := sub_tie_le _ sumFinite
  have same : snapshot.values.get winner = repeatSum stepWord copies := by
    rcases key_inj _ _ key with equal | ⟨_, zero⟩
    · exact equal
    · have zeroKey := zero_key _ zero
      rw [repeatSum_zero] at lead
      have start : Binary32.zero.key = 0 := by decide
      omega
  apply candidates_of_gap snapshot winner (finite winner)
  intro action other
  obtain ⟨fewer, order, below⟩ := trails action other
  have fewerFinite := (freshSum_small .discounted 1 fewer (by omega)).1.1
  have belowKey := (numerical32_order _ _ (finite action) fewerFinite).mp below
  have gap := fresh_lead fewer copies order positive fits
  rw [same]
  exact ⟨finite_not_isNaN (finite action), threshold.1, lt_of_le_of_lt belowKey gap⟩

end Candidate

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
          Kernel.actionAt world (executedAgent agent) start last := by
  obtain ⟨-, ctrlPaid⟩ := loop_quiet primitive perStep agent [] quiet ctrl world start
    (last + 1) young silent fits
  rw [List.nil_append] at ctrlPaid
  obtain ⟨taken, untaken⟩ := loop_totals primitive perStep agent quiet ctrl world start last
    near young silent fits distinct frame fitsFrame
  have counted : ∀ earlier, (frame.indices.countP fun slot =>
      decide (slot ∈ (laidAt agent world start earlier).features.indices)) ≤ 1999 :=
    fun earlier => Nat.le_trans List.countP_le_length fitsFrame
  refine counted_candidate _ _ _ shares (counted last) (fun action => ?_) ?_
    fun action other => ?_
  · rw [tracePolicy_value]
    exact (traces_sum_small ctrlPaid action frame.indices fitsFrame).1.1
  · rw [tracePolicy_value]
    exact taken last 0 rfl
  · rw [tracePolicy_value]
    by_cases once : ∃ earlier, earlier < last + 1 ∧
        Kernel.actionAt world (executedAgent agent) start earlier = action
    · obtain ⟨earlier, early, rfl⟩ := once
      have before : earlier < last := by
        rcases Nat.lt_or_ge earlier last with below | above
        · exact below
        · exact absurd (congrArg _ (by omega : earlier = last)) other
      refine ⟨_, most earlier before, ?_⟩
      rw [taken earlier (last - earlier) (by omega)]
      exact freshSum_older .discounted (last - earlier) _ (by omega) (counted earlier)
    · refine ⟨0, Nat.zero_le _, ?_⟩
      rw [zero_reads (untaken action fun earlier early same => once ⟨earlier, early, same⟩),
        repeatSum_zero, zero_value]

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
      Kernel.actionAt world (executedAgent agent) start last := by
  have chosen := first_choice primitive perStep declared agent [] quiet ctrl world start
    (last + 1) young silent pays fits fitsNext
  have greedy := Explorer.stepOver_greedy ((explorerOf agent.control).after (last + 2))
    (tracePolicy (controlOf (Kernel.memoryAt world (executedAgent agent) start (last + 1)))
      (laidAt agent world start (last + 2)).features declaredRate) unserved calm
  have candidate := (last_candidate primitive perStep agent quiet ctrl world start last near
    (by omega) silent fits distinct (laidAt agent world start (last + 2)).features fitsNext
    shares most declaredRate).2
  rw [chosen, greedy]
  exact candidate _

end Run

end AcornVerif.CurrentTraceCounts
